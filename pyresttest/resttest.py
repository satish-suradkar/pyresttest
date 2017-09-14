#!/usr/bin/env python
import sys
import os
import inspect
import traceback
import yaml
import pycurl
import json
import csv
import logging
import threading
from optparse import OptionParser
from email import message_from_string  # For headers handling
import time
from collections import defaultdict
import json
import string
import collections
import ast
from copy import deepcopy



deferr_flag=False
params_flag=0
is_retried = False #flag to check test is already retried
final_success = 0
final_fail = 0


try:
    from cStringIO import StringIO as MyIO
except:
    try:
        from StringIO import StringIO as MyIO
    except ImportError:
        from io import BytesIO as MyIO

ESCAPE_DECODING = 'string-escape'
# Python 3 compatibility
if sys.version_info[0] > 2:
    from past.builtins import basestring
    from builtins import range as xrange
    ESCAPE_DECODING = 'unicode_escape'

# Dirty hack to allow for running this as a script :-/
if __name__ == '__main__':
    sys.path.append(os.path.dirname(os.path.dirname(
    os.path.realpath(__file__))))
    from six import text_type
    from binding import Context
    import generators
    import validators
    import tests
    from generators import parse_generator
    from parsing import flatten_dictionaries, lowercase_keys, safe_to_bool, safe_to_json
    from workflow import WorkFlow
    from validators import Failure
    from tests import Test, DEFAULT_TIMEOUT
    from benchmarks import Benchmark, AGGREGATES, METRICS, parse_benchmark
else:  # Normal imports
    import six
    from six import text_type

    # Pyresttest internals
    import binding
    from binding import Context
    import generators
    from generators import parse_generator
    import parsing
    from parsing import flatten_dictionaries, lowercase_keys, safe_to_bool, safe_to_json
    import validators
    from validators import Failure
    import tests
    from tests import Test, DEFAULT_TIMEOUT
    import benchmarks
    from benchmarks import Benchmark, AGGREGATES, METRICS, parse_benchmark
    from workflow import WorkFlow

"""
Executable class, ties everything together into the framework.
Module responsibilities:
- Read & import test test_files
- Parse test configs
- Provide executor methods for sets of tests and benchmarks
- Collect and report on test/benchmark results
- Perform analysis on benchmark results
"""
HEADER_ENCODING ='ISO-8859-1' # Per RFC 2616
LOGGING_LEVELS = {'debug': logging.DEBUG,
                  'info': logging.INFO,
                  'warning': logging.WARNING,
                  'error': logging.ERROR,
                  'critical': logging.CRITICAL}

logging.basicConfig(format='%(levelname)s:%(message)s')
logger = logging.getLogger('pyresttest')

DIR_LOCK = threading.RLock()  # Guards operations changing the working directory

test_result = defaultdict(dict)
test_result_out = defaultdict(dict)

class cd:
    """Context manager for changing the current working directory"""
    # http://stackoverflow.com/questions/431684/how-do-i-cd-in-python/13197763#13197763

    def __init__(self, newPath):
        self.newPath = newPath

    def __enter__(self):
        if self.newPath:  # Don't CD to nothingness
            DIR_LOCK.acquire()
            self.savedPath = os.getcwd()
            os.chdir(self.newPath)

    def __exit__(self, etype, value, traceback):
        if self.newPath:  # Don't CD to nothingness
            os.chdir(self.savedPath)
            DIR_LOCK.release()


class TestConfig:
    """ Configuration for a test run """
    timeout = DEFAULT_TIMEOUT  # timeout of tests, in seconds
    print_bodies = False  # Print response bodies in all cases
    print_headers = False  # Print response bodies in all cases
    retries = 0  # Retries on failures
    test_parallel = False  # Allow parallel execution of tests in a test set, for speed?
    interactive = False
    verbose = False
    ssl_insecure = True
    skip_term_colors = False  # Turn off output term colors
    deferred= False
    # Binding and creation of generators
    variable_binds = None
    generators = None  # Map of generator name to generator functionOB

    def __str__(self):
        return json.dumps(self, default=safe_to_json)


class TestSet:
    """ Encapsulates a set of tests and test configuration for them """
    tests = list()
    benchmarks = list()
    config = TestConfig()

    def __init__(self):
        self.config = TestConfig()
        self.tests = list()
        self.benchmarks = list()

    def __str__(self):
        return json.dumps(self, default=safe_to_json)


class BenchmarkResult:
    """ Stores results from a benchmark for reporting use """
    group = None
    name = u'unnamed'

    results = dict()  # Benchmark output, map the metric to the result array for that metric
    aggregates = list()  # List of aggregates, as tuples of (metricname, aggregate, result)
    failures = 0  # Track call count that failed

    def __init__(self):
        self.aggregates = list()
        self.results = list()

    def __str__(self):
        return json.dumps(self, default=safe_to_json)


class TestResponse:
    """ Encapsulates everything about a test response """
    test = None  # Test run
    response_code = None

    body = None  # Response body, if tracked

    passed = False
    response_headers = None
    failures = None

    def __init__(self):
        self.failures = list()

    def __str__(self):
        return json.dumps(self, default=safe_to_json)


def read_test_file(path):
    """ Read test file at 'path' in YAML """
    # TODO allow use of safe_load_all to handle multiple test sets in a given
    # doc
    teststruct = yaml.safe_load(read_file(path))
    return teststruct


def parse_headers(header_string):
    """ Parse a header-string into individual headers
        Implementation based on: http://stackoverflow.com/a/5955949/95122
        Note that headers are a list of (key, value) since duplicate headers are allowed

        NEW NOTE: keys & values are unicode strings, but can only contain ISO-8859-1 characters
    """
    # First line is request line, strip it out
    if not header_string:
        return list()
    request, headers = header_string.split('\r\n', 1)
    if not headers:
        return list()

    # Python 2.6 message header parsing fails for Unicode strings, 2.7 is fine. Go figure.
    if sys.version_info < (2, 7):
        header_msg = message_from_string(headers.encode(HEADER_ENCODING))
        return [(text_type(k.lower(), HEADER_ENCODING), text_type(v, HEADER_ENCODING))
            for k, v in header_msg.items()]
    else:
        header_msg = message_from_string(headers)
        # Note: HTTP headers are *,case-insensitive* per RFC 2616
        return [(k.lower(), v) for k, v in header_msg.items()]


def parse_testsets_included(base_url, test_structure, test_files=set(), working_directory=None, vars=None):
    """ parse all the testcases present in the included files and stores in list """ 
    tests_out = list()
    test_config = TestConfig()
    testsets = list()
    benchmarks = list()
    testsets_included=list()
    include_set=set()
    
    if working_directory is None:
        working_directory = os.path.abspath(os.getcwd())
        
   
    if vars and isinstance(vars, dict):
        test_config.variable_binds = vars
    
    # returns a testconfig and collection of tests
    for node in test_structure:  # Iterate through lists of test and configuration elements
    	
        if isinstance(node, dict):  # Each config element is a miniature key-value dictionary
	    
            node = lowercase_keys(node)
            for key in node:
                
                if key == u'includes': # incllude another file
                    included_file_list = node[key]
                    for file in included_file_list:
                        
                        if file not in test_files:
                            logger.debug("Including supplementary yaml files : " +file)
                            include_set.add(file)
                            import_test_structure = read_test_file(working_directory+"/"+file)
                            included_testsets = parse_testsets(
                                            base_url, import_test_structure, test_files, vars=vars)
                            testsets.extend(included_testsets)  

                if key == u'import':
                    importfile = node[key]  # import another file
                    if importfile not in test_files:
                        logger.debug("Importing test sets: " + importfile)
                        test_files.add(importfile)
                        import_test_structure = read_test_file(importfile)
                        with cd(os.path.dirname(os.path.realpath(importfile))):
                            import_testsets = parse_testsets(
                                base_url, import_test_structure, test_files, vars=vars)
                            testsets.extend(import_testsets)
                elif key == u'url':  # Simple test, just a GET to a URL
                    mytest = Test()
                    val = node[key]
                    assert isinstance(val, basestring)
                    mytest.url = base_url + val
                    tests_out.append(mytest)
                elif key == u'test':  # Complex test with additional parameters
                    child = node[key]
                    mytest = Test.parse_test(base_url, child)
                    tests_out.append(mytest)
                elif key == u'benchmark':
                    benchmark = parse_benchmark(base_url, node[key])
                    benchmarks.append(benchmark)
                elif key == u'config' or key == u'configuration':
                    
                    if(deferr_flag==False):
                        test_config.append(parse_configuration(
                           node[key], base_config=test_config))
                    
            
    
    testset = TestSet()
    testset.tests = tests_out 
    testset.config = test_config
    testset.benchmarks = benchmarks 
    testsets.append(testset)

    return testsets





def unique_name_check(testsets):
    """ It checks for redundant test case name in testsets if found returns False else returns True"""
    list_names=list()
    redundant_flag=True
    for index1 in range(len(testsets)):
        for index2 in range(len(testsets[index1].tests)):
            list_names.append(testsets[index1].tests[index2].name)
    
    for item,count in collections.Counter(list_names).items():
        if(count > 1):
            print("test case "+item+" is repeated more than once")
            return False

    return True
    

def parse_testsets(base_url, test_structure, test_files=set(), command_args=None, vars=None):
    """ Convert a Python data structure read from validated YAML to a set of structured testsets
    The data structure is assumed to be a list of dictionaries, each of which describes:
        - a tests (test structure)
        - a simple test (just a URL, and a minimal test is created)
        - or overall test configuration for this testset
        - an import (load another set of tests into this one, from a separate file)
            - For imports, these are recursive, and will use the parent config if none is present

    Note: test_files is used to track tests that import other tests, to avoid recursive loops

    This returns a list of testsets, corresponding to imported testsets and in-line multi-document sets
    """
    workflow_success = 0
    workflow_fail = 0
    global final_success
    global final_fail
    tests_out = list()
    test_config = TestConfig()
    testsets = list()
    benchmarks = list()
    testsets_included=list()
    include_set=set()

    if(command_args.has_key("I")):
        working_directory = command_args['I']
    
    if working_directory is None:
        working_directory = os.path.abspath(os.getcwd())
        
    if vars and isinstance(vars, dict):
        test_config.variable_binds = vars
    
    
    # returns a testconfig and collection of tests
    parse_order = [u'config',u'benchmark',u'import',u'includes',u'workflow',u'url',u'test']
    for ord in parse_order:
        for node in test_structure:  # Iterate through lists of test and configuration elements
    	    if(ord == node.keys()[0]):
                if isinstance(node, dict):  # Each config element is a miniature key-value dictionary
	    
                    node = lowercase_keys(node)
                    
                    for key in node:
                        if key == u'includes':
                            included_file_list = node[key]
                            for file in included_file_list:
                                if file not in test_files:
                                    logger.debug("Including supplementary yaml files : " +file)
                                    include_set.add(file)
                                    
                                    import_test_structure = read_test_file(working_directory+"/"+file)
 				   
                                    included_testsets = parse_testsets(
                                            base_url, import_test_structure, test_files,command_args=command_args, vars=vars)
                                    
                                    testsets.extend(included_testsets)
                            continue   
                            
                           
                        if key == u'workflow':  # Workflow containing set of test cases in given order
                            
                            if(unique_name_check(testsets) == False):
                                raise Exception("Redundant Test Case Found")
                            child = node[key]
                            
                            myworkflow = WorkFlow.parse_workflow(base_url, child,global_gen=test_config.generators)
			  
                            if(deferr_flag==True): 
                               workflow_flag = run_include_testsets(testsets,myworkflow,test_config.generators,command_args=command_args,deferr_flag=True)
                            
                            if(workflow_flag == True):
                                workflow_success = workflow_success+1
                            else:
   			        workflow_fail = workflow_fail+ 1	  
			    continue   	  
					                    
                    

                        if key == u'import':   # import another file
                            importfile = node[key] 
                            if importfile not in test_files:
                                logger.debug("Importing test sets: " + importfile)
                                test_files.add(importfile)
                                import_test_structure = read_test_file(importfile)
                                with cd(os.path.dirname(os.path.realpath(importfile))):
                                    import_testsets = parse_testsets(
                                         base_url, import_test_structure, test_files,command_args=command_args,vars=vars)
                                    testsets.extend(import_testsets)
                            continue

                        if key == u'url':  # Simple test, just a GET to a URL
                            mytest = Test()
                            val = node[key]
                            assert isinstance(val, basestring)
                    	    mytest.url = base_url + val
                    	    tests_out.append(mytest)
                            continue

                        if key == u'test':  # Complex test with additional parameters
                            child = node[key]
                            mytest = Test.parse_test(base_url, child)
                            tests_out.append(mytest)
                            continue

                        if key == u'benchmark':
                            benchmark = parse_benchmark(base_url, node[key])
                            benchmarks.append(benchmark)
 			    continue

                        if key == u'config' or key == u'configuration':
                            test_config = parse_configuration(
                                          node[key], base_config=test_config ,working_directory=working_directory)
                            deferr_flag=test_config.deferred
   			    continue
    
    final_success = workflow_success
    final_fail = workflow_fail
    testset = TestSet()
    testset.tests = tests_out 
    testset.config = test_config
    testset.benchmarks = benchmarks 
    testsets.append(testset)
    
    return testsets



def parse_configuration(node, base_config=None , working_directory=None):
    """ Parse input config to configuration information """
    
    test_config = base_config
    if not test_config:
        test_config = TestConfig()
    
    node = lowercase_keys(flatten_dictionaries(node))  # Make it usable
    
    for key, value in node.items():
        if key == u'timeout':
            test_config.timeout = int(value)
        elif key == u'print_bodies':
            test_config.print_bodies = safe_to_bool(value)
        elif key == u'retries':
            test_config.retries = int(value)
        elif key == u'delay':
            test_config.delay = int(value)
        elif key == u'variable_binds':
            if not test_config.variable_binds:
                test_config.variable_binds = dict()
            test_config.variable_binds.update(flatten_dictionaries(value))
        elif key == u'generators':
            flat = flatten_dictionaries(value)
            gen_map = dict()
            for generator_name, generator_config in flat.items():
                temp = generator_config['start']
                generator_config['start'] = working_directory+"/"+temp 
                gen = parse_generator(generator_config)
                gen_map[str(generator_name)] = gen
            test_config.generators = gen_map
        elif key == u'deferred':
            test_config.deferred = safe_to_bool(value)
            
    
    return test_config


def read_file(path):
    """ Read an input into a file, doing necessary conversions around relative path handling """
    with open(path, "r") as f:
        string = f.read()
        f.close()
    return string



def run_test(mytest, test_config=TestConfig(), context=None, curl_handle=None,repeat_no = 0,working_directory= None, *args, **kwargs):
    """ Put together test pieces: configure & run actual test, return results """
     
    # Initialize a context if not supplied
    my_context = context
    if my_context is None:
        my_context = Context()
  
    
    mytest.update_context_before(my_context)
    
    templated_test = mytest.realize(my_context)
    
    if(isinstance(mytest.expected_status,str)): 
        temp = templated_test.expected_status    
        mytest.__setattr__("expected_status",ast.literal_eval(temp))    
    
    curl = templated_test.configure_curl(
        timeout=test_config.timeout, context=my_context, curl_handle=curl_handle)
    result = TestResponse()
    
    result.test = templated_test
     
    # reset the body, it holds values from previous runs otherwise
    headers = MyIO()
    body = MyIO()
    curl.setopt(pycurl.WRITEFUNCTION, body.write)
    curl.setopt(pycurl.HEADERFUNCTION, headers.write)
    if test_config.verbose:
        curl.setopt(pycurl.VERBOSE, True)
    if test_config.ssl_insecure:
        curl.setopt(pycurl.SSL_VERIFYPEER, 0)
        curl.setopt(pycurl.SSL_VERIFYHOST, 0)

    result.passed = None

    if test_config.interactive:
        print("===================================")
        print("%s" % mytest.name)
        print("-----------------------------------")
        print("REQUEST:")
        print("%s %s" % (templated_test.method, templated_test.url))
        print("HEADERS:")
        print("%s" % (templated_test.headers))
        if mytest.body is not None:
            print("\n%s" % templated_test.body)
        raw_input("Press ENTER when ready (%d): " % (mytest.delay))


    for test_need in mytest.depends_on:
        if not test_result[test_need]['result'] or test_result[test_need]['result'] == 'skip':
            print "\n\033[1;31m 'test: {0}' depends on 'test: {1}' \033[0m".format(mytest.name, test_need)
            return

    try:
        curl.perform()  # Run the actual call
    except Exception as e:
        # Curl exception occurred (network error), do not pass go, do not
        # collect $200
        trace = traceback.format_exc()
        result.failures.append(Failure(message="Curl Exception: {0}".format(
            e), details=trace, failure_type=validators.FAILURE_CURL_EXCEPTION))
        result.passed = False
        curl.close()
        return result 

    # Retrieve values
    result.body = body.getvalue()
    body.close()
    result.response_headers = text_type(headers.getvalue(), HEADER_ENCODING)  # Per RFC 2616
    headers.close()

    response_code = curl.getinfo(pycurl.RESPONSE_CODE)
    result.response_code = response_code
    
    logger.debug("Initial Test Result, based on expected response code: " +
                 str(response_code in mytest.expected_status))
    
    flag = 0
    global is_retried
    retry = 0

    if mytest.retries >= 0:
        
        retry = mytest.retries
        flag = 1
        is_retried = True
    elif not is_retried:
        retry = test_config.retries
        flag = 2
   
    
    if response_code in mytest.expected_status:
        result.passed = True
        if(repeat_no != 0):
            with open(working_directory+"/test_stat.txt", "a") as myfile:
                dict_dump = context.variables
                dict_dump["result"] = "PASSED"
                myfile.write(str(dict_dump)+",")
            number = repeat_no
	    while(number != 0):   
                number = number-1        
                return run_test(mytest, test_config, context, curl_handle ,working_directory=working_directory,repeat_no=number)
                    
        

    else:
        if(repeat_no != 0):
            retry = repeat_no
        # if retry not define
        
        if retry == 0:
            # Invalid response code
            result.passed = False
            failure_message = "Invalid HTTP response code: response code {0} not in expected codes [{1}]".format(
                response_code, mytest.expected_status)
            result.failures.append(Failure(
                message=failure_message, details=None, failure_type=validators.FAILURE_INVALID_RESPONSE))
            
        # retry test
        else:
           # with open(working_directory+"/test_stat.txt", "a") as myfile:
           #     dict_dump = context.variables
           #     dict_dump["result"] = "FAILED"
           #     myfile.write(str(dict_dump)+",")
            retry -= 1
            #retry from test
            if flag == 1:
                mytest.retries = retry
                time.sleep(mytest.delay)
                return run_test(mytest, test_config, context, curl_handle,working_directory=working_directory)

            #retry from config
            if flag == 2:
                test_config.retries = retry
                time.sleep(test_config.delay)
                return run_test(mytest, test_config, context, curl_handle,working_directory=working_directory)


    # Parse HTTP headers
    try:
        result.response_headers = parse_headers(result.response_headers)
    except Exception as e:
        trace = traceback.format_exc()
        result.failures.append(Failure(message="Header parsing exception: {0}".format(
            e), details=trace, failure_type=validators.FAILURE_TEST_EXCEPTION))
        result.passed = False
        curl.close()
        return result

    # print str(test_config.print_bodies) + ',' + str(not result.passed) + ' ,
    # ' + str(test_config.print_bodies or not result.passed)

    head = result.response_headers
    # execute validator on body
    #if result.passed is True:
    body = result.body

    if mytest.validators is not None and isinstance(mytest.validators, list):
        logger.debug("executing this many validators: " +
                         str(len(mytest.validators)))
        failures = result.failures
        for validator in mytest.validators:
            validate_result = validator.validate(
                    body=body, headers=head, context=my_context)
            if not validate_result:
                if(mytest.retries):
                    retry -= 1
                    #retry from test
                    if flag == 1:
                        mytest.retries = retry
                        time.sleep(mytest.delay)
                        return run_test(mytest, test_config, context, curl_handle,working_directory=working_directory)

                    #retry from config 
                    if flag == 2:
                        print(result.body)
                        test_config.retries = retry
                        time.sleep(test_config.delay)
                        return run_test(mytest, test_config, context, curl_handle,working_directory=working_directory)

                result.passed = False
            else:
                result.passed = True
            # Proxy for checking if it is a Failure object, because of
            # import issues with isinstance there
            if hasattr(validate_result, 'details'):
                failures.append(validate_result)
            # TODO add printing of validation for interactive mode
    else:
        logger.debug("no validators found")
       
    # Only do context updates if test was successful
    if(result.passed == True):
        mytest.update_context_after(result.body, head, my_context)

    # Print response body if override is set to print all *OR* if test failed
    # (to capture maybe a stack trace)
    if test_config.print_bodies or not result.passed:
        if test_config.interactive:
            print("RESPONSE:")
        print(result.body.decode(ESCAPE_DECODING))

    if test_config.print_headers or not result.passed:
        if test_config.interactive:
            print("RESPONSE HEADERS:")
        print(result.response_headers)

    # TODO add string escape on body output
    logger.debug(result)

    return result


def run_benchmark(benchmark, test_config=TestConfig(), context=None, *args, **kwargs):
    """ Perform a benchmark, (re)using a given, configured CURL call to do so
        The actual analysis of metrics is performed separately, to allow for testing
    """

    # Context handling
    my_context = context
    if my_context is None:
        my_context = Context()

    warmup_runs = benchmark.warmup_runs
    benchmark_runs = benchmark.benchmark_runs
    message = ''  # Message is name of benchmark... print it?

    if (benchmark_runs <= 0):
        raise Exception(
            "Invalid number of benchmark runs, must be > 0 :" + benchmark_runs)

    result = TestResponse()

    # TODO create and use a curl-returning configuration function
    # TODO create and use a post-benchmark cleanup function
    # They should use is_dynamic/is_context_modifier to determine if they need to
    #  worry about context and re-reading/retemplating and only do it if needed
    #    - Also, they will need to be smart enough to handle extraction functions
    #  For performance reasons, we don't want to re-run templating/extraction if
    #   we do not need to, and do not want to save request bodies.

    # Initialize variables to store output
    output = BenchmarkResult()
    output.name = benchmark.name
    output.group = benchmark.group
    metricnames = list(benchmark.metrics)
    # Metric variable for curl, to avoid hash lookup for every metric name
    metricvalues = [METRICS[name] for name in metricnames]
    # Initialize arrays to store results for each metric
    results = [list() for x in xrange(0, len(metricnames))]
    curl = pycurl.Curl()

    # Benchmark warm-up to allow for caching, JIT compiling, on client
    logger.info('Warmup: ' + message + ' started')
    for x in xrange(0, warmup_runs):
        benchmark.update_context_before(my_context)
        templated = benchmark.realize(my_context)
        curl = templated.configure_curl(
            timeout=test_config.timeout, context=my_context, curl_handle=curl)
        # Do not store actual response body at all.
        curl.setopt(pycurl.WRITEFUNCTION, lambda x: None)
        curl.perform()

    logger.info('Warmup: ' + message + ' finished')

    logger.info('Benchmark: ' + message + ' starting')

    for x in xrange(0, benchmark_runs):  # Run the actual benchmarks
        # Setup benchmark
        benchmark.update_context_before(my_context)
        templated = benchmark.realize(my_context)
        curl = templated.configure_curl(
            timeout=test_config.timeout, context=my_context, curl_handle=curl)
        # Do not store actual response body at all.
        curl.setopt(pycurl.WRITEFUNCTION, lambda x: None)

        try:  # Run the curl call, if it errors, then add to failure counts for benchmark
            curl.perform()
        except Exception:
            output.failures = output.failures + 1
            curl.close()
            curl = pycurl.Curl()
            continue  # Skip metrics collection

        # Get all metrics values for this run, and store to metric lists
        for i in xrange(0, len(metricnames)):
            results[i].append(curl.getinfo(metricvalues[i]))

    logger.info('Benchmark: ' + message + ' ending')

    temp_results = dict()
    for i in xrange(0, len(metricnames)):
        temp_results[metricnames[i]] = results[i]
    output.results = temp_results
    return analyze_benchmark_results(output, benchmark)


def analyze_benchmark_results(benchmark_result, benchmark):
    """ Take a benchmark result containing raw benchmark results, and do aggregation by
    applying functions

    Aggregates come out in format of metricname, aggregate_name, result """

    output = BenchmarkResult()
    output.name = benchmark_result.name
    output.group = benchmark_result.group
    output.failures = benchmark_result.failures

    # Copy raw metric arrays over where necessary
    raw_results = benchmark_result.results
    temp = dict()
    for metric in benchmark.raw_metrics:
        temp[metric] = raw_results[metric]
    output.results = temp

    # Compute aggregates for each metric, and add tuples to aggregate results
    aggregate_results = list()
    for metricname, aggregate_list in benchmark.aggregated_metrics.items():
        numbers = raw_results[metricname]
        for aggregate_name in aggregate_list:
            if numbers:  # Only compute aggregates if numbers exist
                aggregate_function = AGGREGATES[aggregate_name]
                aggregate_results.append(
                    (metricname, aggregate_name, aggregate_function(numbers)))
            else:
                aggregate_results.append((metricname, aggregate_name, None))

    output.aggregates = aggregate_results
    return output


def metrics_to_tuples(raw_metrics):
    """ Converts metric dictionary of name:values_array into list of tuples
        Use case: writing out benchmark to CSV, etc

        Input:
        {'metric':[value1,value2...], 'metric2':[value1,value2,...]...}

        Output: list, with tuple header row, then list of tuples of values
        [('metric','metric',...), (metric1_value1,metric2_value1, ...) ... ]
    """
    if not isinstance(raw_metrics, dict):
        raise TypeError("Input must be dictionary!")

    metrics = sorted(raw_metrics.keys())
    arrays = [raw_metrics[metric] for metric in metrics]

    num_rows = len(arrays[0])  # Assume all same size or this fails
    output = list()
    output.append(tuple(metrics))  # Add headers

    # Create list of tuples mimicking 2D array from input
    for row in xrange(0, num_rows):
        new_row = tuple([arrays[col][row] for col in xrange(0, len(arrays))])
        output.append(new_row)
    return output


def write_benchmark_json(file_out, benchmark_result, benchmark, test_config=TestConfig()):
    """ Writes benchmark to file as json """
    json.dump(benchmark_result, file_out, default=safe_to_json)


def write_benchmark_csv(file_out, benchmark_result, benchmark, test_config=TestConfig()):
    """ Writes benchmark to file as csv """
    writer = csv.writer(file_out)
    writer.writerow(('Benchmark', benchmark_result.name))
    writer.writerow(('Benchmark Group', benchmark_result.group))
    writer.writerow(('Failures', benchmark_result.failures))

    # Write result arrays
    if benchmark_result.results:
        writer.writerow(('Results', ''))
        writer.writerows(metrics_to_tuples(benchmark_result.results))
    if benchmark_result.aggregates:
        writer.writerow(('Aggregates', ''))
        writer.writerows(benchmark_result.aggregates)

# Method to call when writing benchmark file
OUTPUT_METHODS = {u'csv': write_benchmark_csv, u'json': write_benchmark_json}


def log_failure(failure, context=None, test_config=TestConfig()):
    """ Log a failure from a test """
    logger.error("Test Failure, failure type: {0}, Reason: {1}".format(
        failure.failure_type, failure.message))
    if failure.details:
        logger.error("Validator/Error details:" + str(failure.details))


def run_tests_list(mytests,myconfig,context):
    group_failure_counts = dict()
    total_failures = 0
    myinteractive = False
    curl_handle = pycurl.Curl()
    group_results = dict() 
    
    for test in mytests:
            # Initialize the dictionaries to store test fail counts and results
            if test.group not in group_results:
                group_results[test.group] = list()
                group_failure_counts[test.group] = 0

            global is_retried
            is_retried = False 
           
            result = run_test(test, test_config=myconfig, context=context, curl_handle=curl_handle)
            if result is not None:
                test_result[test.name]['result'] = result.passed
                if not result.passed:
                    if hasattr(result, 'failures'):
                        error_str = ''.join(str(e) for e in result.failures)
                        test_result_out[result.test.name.strip()]['error_msg'] = error_str
                    test_result[test.name]['expected_status'] = test.expected_status

            if result is None:
                skip += 1
                test_result[test.name]['result'] = "skip"
                test_result[test.name]['depends_on'] = test.depends_on
                continue

            result.body = None  # Remove the body, save some memory!
            if not result.passed:  # Print failure, increase failure counts for that test group
            # Use result test URL to allow for templating
                logger.error('Test Failed: ' + test.name + " URL=" + result.test.url +
                         " Group=" + test.group + " HTTP Status Code: " + str(result.response_code))
                # Print test failure reasons
                if result.failures:
                    for failure in result.failures:
                        log_failure(failure, context=context,
                                    test_config=myconfig)
                # Increment test failure counts for that group (adding an entry
                # if not present)
                failures = group_failure_counts[test.group]
                failures = failures + 1
                group_failure_counts[test.group] = failures

            else:  # Test passed, print results
                logger.info('Test Succeeded: ' + test.name +
                    " URL=" + test.url + " Group=" + test.group)

            # Add results for this test group to the resultset
            group_results[test.group].append(result)

            # handle stop_on_failure flag
            if not result.passed and test.stop_on_failure is not None and test.stop_on_failure:
                print(
                    'STOP ON FAILURE! stopping test set execution, continuing with other test sets')
                break




def run_include_testsets(testsets1,myworkflow,global_generators,command_args = None,deferr_flag=False):
    """ execute  a test from included yaml file """

    
    flow = myworkflow.tests
    params = myworkflow.params
    params_templated = myworkflow.params_templated
    generator_binds = myworkflow.generator_binds   
    group_results = dict() 
    group_failure_counts = dict()
    total_failures = 0
    myinteractive = False
    curl_handle = pycurl.Curl()
    context = Context()
    depends_list=list()
    exit_flag = False    
    succeeded_test_count = 0
    context.__setattr__('generator_binds',generator_binds)
        
    if(command_args.has_key("I")):
        working_directory = command_args['I']

    if working_directory is None:
        working_directory = os.path.abspath(os.getcwd())

    for i in flow:
        if(exit_flag == True):
            break
        for testset in testsets1:
            mytests = deepcopy(testset.tests)           
            myconfig = testset.config
            
            if(deferr_flag==True):
                if(myconfig.generators):
                    if(global_generators):
                        for gen_name,gen_obj in global_generators.items():
                            myconfig.generators[gen_name]=gen_obj
                else:
                    myconfig.generators=global_generators

            mybenchmarks = testset.benchmarks
            
            
	               
            # Bind variables & add generators if pertinent
            if myconfig.variable_binds:
                context.bind_variables(myconfig.variable_binds)
            if myconfig.generators:
                for key, value in myconfig.generators.items():
                    context.add_generator(key, value)
            
            # Make sure we actually have tests to execute
            if not mytests:
                # no tests in this test set, probably just imports.. skip to next
                # test set
                break

            myinteractive = True if myinteractive or myconfig.interactive else False

            skip = 0
            # Run tests, collecting statistics as needed

            
            for test in mytests:
                
                if(i.strip() == test.name.strip()):
                    
                    if(context.generator_binds and test.generator_binds):
                        for var_name,gen_name in context.generator_binds.items():
                            test.generator_binds[var_name]=gen_name
                            
                    if(params):
                        
                        s=str()
                        if(test.name in params.keys()):
                            for t in range(len(params[test.name])):
   			        for old,new in params[test.name][t].items():
                                    s=new
                                    test.__setattr__(old,new)
                        
                        if(params_templated):
                             if(test.name in params_templated.keys()):
                                 
                                 if(test.templates is None):
                                     test.templates=dict()
                                 templated_params_list=params_templated[test.name]

                                 for para in templated_params_list: 
                                     for t in range(len(params[test.name])):
                                         for old,new in params[test.name][t].items():
                                             if(para==old):  
                                                 
                                                 test.templates[para] = string.Template(new)  
                        
                        if(test.repeat): 
                            repeat = test.repeat
                        else:
                            repeat = 0
		                
                        result = run_test(test,test_config=myconfig, context=context, curl_handle=curl_handle,repeat_no = repeat,working_directory = working_directory)    
                         		             
                    if(not params):
	                result = run_test(test, test_config=myconfig, context=context, curl_handle=curl_handle)
                        
                    
                    # Initialize the dictionaries to store test fail counts and results
                    if test.group not in group_results:
                        group_results[test.group] = list()
                        group_failure_counts[test.group] = 0

                    global is_retried
                    is_retried = False
                    #print "\n ============================================================= \n"
                
                    

                    if result is not None:                       
                        if result.test.display_name is not None:
                            test_result_out[result.test._display_name.strip()]['result'] = result.passed
                            if not result.passed:
                                if hasattr(result, 'failures'):
                                    error_str = ''.join(str(e) for e in result.failures)
                                    test_result_out[result.test._display_name.strip()]['error_msg'] = error_str
#                                if 'body' in json.loads(result.__str__()).keys():
#                                    test_result[test.name.strip()]['body'] = result.body 
                        else:
                            test_result_out[test.name.strip()]['result'] = result.passed
                            if not result.passed:
                                if hasattr(result, 'failures'):
                                    error_str = ''.join(str(e) for e in result.failures)
                                    test_result_out[test.name.strip()]['error_msg'] = error_str
#                                if 'body' in json.loads(result.__str__()).keys():
#                                    test_result[test.name.strip()]['body'] = result.body
                                
 
                    if result is None:
                        skip += 1
                        if result.test._display_name is not None:
                            test_result_out[result.test._display_name.strip()]['result'] = "skip"
                            test_result_out[result.test._display_name.strip()]['depends_on'] = test.depends_on
                        else:
                            test_result_out[test.name.strip()]['result'] = "skip"
                            test_result_out[test.name.strip()]['depends_on'] = test.depends_on
                        continue



                    if result is not None:
                        test_result[test.name.strip()]['result'] = result.passed
                        if not result.passed:
                            if hasattr(result, 'failures'):
                                error_str = ''.join(str(e) for e in result.failure)
                                test_result[test.name.strip()]['error_msg'] = error_str
                            test_result[test.name.strip()]['expected_status'] = test.expected_status

                    if result is None:
		                skip += 1
		                test_result[test.name.strip()]['result'] = "skip"
		                test_result[test.name.strip()]['depends_on'] = test.depends_on
		                continue

                
	            result.body = None  # Remove the body, save some memory!
	            if not result.passed:  # Print failure, increase failure counts for that test group
	               # Use result test URL to allow for templating
		        logger.error('Test Failed: ' + test.name + " URL=" + result.test.url +
		         " Group=" + test.group + " HTTP Status Code: " + str(result.response_code))
		       #  Print test failure reasons
		        if result.failures:
		            for failure in result.failures:
		                log_failure(failure, context=context,
		                    test_config=myconfig)
		        # Increment test failure counts for that group (adding an entry
		        #  if not present)
		        failures = group_failure_counts[test.group]
		        failures = failures + 1
		        group_failure_counts[test.group] = failures

	            else:  # Test passed, print results
		            logger.info('Test Succeeded: ' + test.name +
		               " URL=" + test.url + " Group=" + test.group)

	            # Add results for this test group to the resultset
	            group_results[test.group].append(result)

                    if(result.passed == False):
                            print("\n"+test.name+" failed ")
                            exit_flag = True
                            break
                    else:
                        succeeded_test_count += 1

	            # handle stop_on_failure flag
	            if not result.passed and test.stop_on_failure is not None and test.stop_on_failure:
		        print(
		                'STOP ON FAILURE! stopping test set execution, continuing with other test sets')
		        break
                    break

                    

       
    #print "\n ==================================================== \n"
    if myinteractive:
        # a break for when interactive bits are complete, before summary data
        print("===================================")
  
    # Print summary results
    for group in sorted(group_results.keys()):
       
        if(deferr_flag == True):
            test_count = len(flow)
            failures = test_count - succeeded_test_count
            skip = failures
        else:
            test_count = len(group_results[group])
            failures = group_failure_counts[group]

        total_failures = total_failures + failures
       
        passfail = {True: u'SUCCEEDED: ', False: u'FAILED: '}
        output_string = "Test Group {0} {1}: {2}/{3} Tests Passed!\nTest Group {0} SKIPPED: {4}"\
              .format(group, passfail[failures == 0], str(test_count - failures), str(test_count), str(skip)) 

        with open('test_result.json', 'w') as out:
            json.dump(test_result_out, out, indent=4)

       
        if command_args['skip_term_colors']:
            print(output_string)
        else:
            if failures > 0:
                print('\033[91m' + output_string + '\033[0m')
            else: 
                print('\033[92m' + output_string + '\033[0m')
    
    
    if(deferr_flag == True):
        out_string = " Workflow {0} : SUCCEEDED ".format(myworkflow.name)
        fail_flag = False
           
        for test_name in flow: 
            if('result' not in test_result[test_name.strip()].keys() or test_result[test_name]['result'] == False):
                out_string = " Workflow {0} : FAILED ".format(myworkflow.name)
                if command_args['skip_term_colors']:
                    print(out_string)
                else:
                    print('\033[91m' + out_string + '\033[0m')
                fail_flag = True
                break
            
        if(fail_flag == False):
            if command_args['skip_term_colors']:
                print(out_string)
            else:
                print('\033[92m' + out_string + '\033[0m')
            
                           
    if(total_failures > 0):
        return False       
    else:
        return True


def run_testsets(testsets):
    """ Execute a set of tests, using given TestSet list input """
    group_results = dict()  # results, by group
    group_failure_counts = dict()
    total_failures = 0
    myinteractive = False
    ssl_insecure=True
    curl_handle = pycurl.Curl()
    
    for testset in testsets:
        mytests = testset.tests
        myconfig = testset.config
        mybenchmarks = testset.benchmarks
        context = Context()

        
        # Bind variables & add generators if pertinent
        if myconfig.variable_binds:
            context.bind_variables(myconfig.variable_binds)
        if myconfig.generators:
            for key, value in myconfig.generators.items():
                context.add_generator(key, value)

        # Make sure we actually have tests to execute
        if not mytests and not mybenchmarks:
            # no tests in this test set, probably just imports.. skip to next
            # test set
            break

        myinteractive = True if myinteractive or myconfig.interactive else False

        skip = 0
        # Run tests, collecting statistics as needed
        for test in mytests:
            # Initialize the dictionaries to store test fail counts and results
            if test.group not in group_results:
                group_results[test.group] = list()
                group_failure_counts[test.group] = 0

            global is_retried
            is_retried = False
            #print "\n =========================*=========================== \n"
            
            
            result = run_test(test, test_config=myconfig, context=context, curl_handle=curl_handle)
            if result is not None:
                
                test_result[test.name]['result'] = result.passed
                if not result.passed:
                    if hasattr(result, 'failures'):
                        error_str = ''.join(str(e) for e in result.failures) 
                        test_result[test.name.strip()]['error_msg'] = error_str
                    #if 'body' in json.loads(result.__str__()).keys():
                    #    test_result[test.name.strip()]['body'] = result.body
                    #    if 'details' in json.loads(result.__str__())['body'].keys():
                    #        test_result[test.name.strip()]['details'] = result.body.details
                    #if 'details' in json.loads(result.__str__()).keys():
                    
                    #    test_result[test.name.strip()]['details'] = json.loads(result.__str__())['details']
                    test_result[test.name]['expected_status'] = test.expected_status

            if result is None:
                skip += 1
                test_result[test.name]['result'] = "skip"
                test_result[test.name]['depends_on'] = test.depends_on
                continue

            result.body = None  # Remove the body, save some memory!
            if not result.passed:  # Print failure, increase failure counts for that test group
            # Use result test URL to allow for templating
                logger.error('Test Failed: ' + test.name + " URL=" + result.test.url +
                         " Group=" + test.group + " HTTP Status Code: " + str(result.response_code))
                # Print test failure reasons
                if result.failures:
                    for failure in result.failures:
                        log_failure(failure, context=context,
                                    test_config=myconfig)
                # Increment test failure counts for that group (adding an entry
                # if not present)
                failures = group_failure_counts[test.group]
                failures = failures + 1
                group_failure_counts[test.group] = failures

            else:  # Test passed, print results
                logger.info('Test Succeeded: ' + test.name +
                    " URL=" + test.url + " Group=" + test.group)

            # Add results for this test group to the resultset
            group_results[test.group].append(result)

            # handle stop_on_failure flag
            if not result.passed and test.stop_on_failure is not None and test.stop_on_failure:
                print(
                    'STOP ON FAILURE! stopping test set execution, continuing with other test sets')
                break

        for benchmark in mybenchmarks:  # Run benchmarks, analyze, write
            if not benchmark.metrics:
                logger.debug('Skipping benchmark, no metrics to collect')
                continue

            logger.info("Benchmark Starting: " + benchmark.name +
                        " Group: " + benchmark.group)
            benchmark_result = run_benchmark(
                benchmark, myconfig, context=context)
            print(benchmark_result)
            logger.info("Benchmark Done: " + benchmark.name +
                        " Group: " + benchmark.group)

            if benchmark.output_file:  # Write file
                logger.debug(
                    'Writing benchmark to file in format: ' + benchmark.output_format)
                write_method = OUTPUT_METHODS[benchmark.output_format]
                my_file = open(benchmark.output_file, 'w')  # Overwrites file
                logger.debug("Benchmark writing to file: " +
                             benchmark.output_file)
                write_method(my_file, benchmark_result,
                             benchmark, test_config=myconfig)
                my_file.close()
    #print "\n ==================================================== \n"
    if myinteractive:
        # a break for when interactive bits are complete, before summary data
        print("===================================")

    # Print summary results
    for group in sorted(group_results.keys()):
        test_count = len(group_results[group])
        failures = group_failure_counts[group]
        total_failures = total_failures + failures

        passfail = {True: u'SUCCEEDED: ', False: u'FAILED: '}
        output_string = "Test Group {0} {1}: {2}/{3} Tests Passed!\nTest Group {0} SKIPPED: {4}"\
            .format(group, passfail[failures == 0], str(test_count - failures), str(test_count), str(skip)) 

        with open('test_result.json', 'w') as out:
            json.dump(test_result, out, indent=4)


        if myconfig.skip_term_colors:
            print(output_string)
        else:
            if failures > 0:
                print('\033[91m' + output_string + '\033[0m')
            else:
                print('\033[92m' + output_string + '\033[0m')

    return total_failures


def register_extensions(modules):
    """ Import the modules and register their respective extensions """
    if isinstance(modules, basestring):  # Catch supplying just a string arg
        modules = [modules]
    for ext in modules:
        # Get the package prefix and final module name
        segments = ext.split('.')
        module = segments.pop()
        package = '.'.join(segments)
        # Necessary to get the root module back
        module = __import__(ext, globals(), locals(), package)

        # Extensions are registered by applying a register function to sets of
        # registry name/function pairs inside an object
        extension_applies = {
            'VALIDATORS': validators.register_validator,
            'COMPARATORS': validators.register_comparator,
            'VALIDATOR_TESTS': validators.register_test,
            'EXTRACTORS': validators.register_extractor,
            'GENERATORS': generators.register_generator
        }

        has_registry = False
        for registry_name, register_function in extension_applies.items():
            if hasattr(module, registry_name):
                registry = getattr(module, registry_name)
                for key, val in registry.items():
                    register_function(key, val)
                if registry:
                    has_registry = True

        if not has_registry:
            raise ImportError(
                "Extension to register did not contain any registries: {0}".format(ext))

# AUTOIMPORTS, these should run just before the main method, to ensure
# everything else is loaded
try:
    import jsonschema
    register_extensions('pyresttest.ext.validator_jsonschema')
except ImportError as ie:
    logging.debug(
        "Failed to load jsonschema validator, make sure the jsonschema module is installed if you wish to use schema validators.")

try:
    import jmespath
    register_extensions('pyresttest.ext.extractor_jmespath')
except ImportError as ie:
    logging.debug(
        "Failed to load jmespath extractor, make sure the jmespath module is installed if you wish to use jmespath extractor.")

def main(args):
    """
    Execute a test against the given base url.

    Keys allowed for args:
        url           - REQUIRED - Base URL
        test          - REQUIRED - Test file (yaml)
        print_bodies  - OPTIONAL - print response body
        print_headers  - OPTIONAL - print response headers
        log           - OPTIONAL - set logging level {debug,info,warning,error,critical} (default=warning)
        interactive   - OPTIONAL - mode that prints info before and after test exectuion and pauses for user input for each test
        absolute_urls - OPTIONAL - mode that treats URLs in tests as absolute/full URLs instead of relative URLs
        skip_term_colors - OPTIONAL - mode that turn off the output term colors
    """
    
    

    if 'log' in args and args['log'] is not None:
        logger.setLevel(LOGGING_LEVELS.get(
            args['log'].lower(), logging.NOTSET))

    if 'import_extensions' in args and args['import_extensions']:
        extensions = args['import_extensions'].split(';')


        # We need to add current folder to working path to import modules
        if not args['I']:
            working_folder=os.path.realpath(os.path.abspath(os.getcwd()))    
        else:
            working_folder = args['I']
        if working_folder not in sys.path:
            sys.path.insert(0, working_folder)
        register_extensions(extensions)
    
    if not args['I']:
        working_folder=os.path.realpath(os.path.abspath(os.getcwd()))    
        test_file = args['test'] 
        test_structure = read_test_file(test_file)  
    else:
        working_folder = args['I']
        test_file = args['test']
        test_structure = read_test_file(working_folder+"/"+test_file)

    my_vars = None
    if 'vars' in args and args['vars'] is not None:
        my_vars = yaml.safe_load(args['vars'])
    if my_vars and not isinstance(my_vars, dict):
        raise Exception("Variables must be a dictionary!")

    # Set up base URL
    base_url = args['url']

    if 'absolute_urls' in args and args['absolute_urls']:
        base_url = ''
    
    
    tests = parse_testsets(base_url, test_structure,
                           command_args=args, vars=my_vars)
    
    
    
    # Override configs from command line if config set
    for t in tests:
        if 'print_bodies' in args and args['print_bodies'] is not None and bool(args['print_bodies']):
            t.config.print_bodies = safe_to_bool(args['print_bodies'])

        if 'print_headers' in args and args['print_headers'] is not None and bool(args['print_headers']):
            t.config.print_headers = safe_to_bool(args['print_headers'])

        if 'interactive' in args and args['interactive'] is not None:
            t.config.interactive = safe_to_bool(args['interactive'])

        if 'verbose' in args and args['verbose'] is not None:
            t.config.verbose = safe_to_bool(args['verbose'])

        if 'ssl_insecure' in args and args['ssl_insecure'] is not None:
            t.config.ssl_insecure = safe_to_bool(args['ssl_insecure'])

        if 'skip_term_colors' in args and args['skip_term_colors'] is not None:
            t.config.skip_term_colors = safe_to_bool(args['skip_term_colors'])

    
    if((final_fail+final_success)>0):
        if(args['skip_term_colors'] == True):
            print("\nTotal Workflows: "+str(final_fail+final_success))
            print("Total Succeeded Workflows: "+str(final_success))
            print("Total Failed Workflows: "+str(final_fail))
        else:
            if(final_fail > 0):
                print('\033[91m'+"\nTotal Workflows: "+str(final_fail+final_success)+'\033[0m')
            	print('\033[91m'+"Total Succeeded Workflows: "+str(final_success)+'\033[0m')
            	print('\033[91m'+"Total Failed Workflows: "+str(final_fail)+'\033[0m')
       	    else:
            	print('\033[92m'+"\nTotal Workflows: "+str(final_fail+final_success)+'\033[0m')
            	print('\033[92m'+"Total Succeeded Workflows: "+str(final_success)+'\033[0m')
            	print('\033[92m'+"Total Failed Workflows: "+str(final_fail)+'\033[0m')
        sys.exit(final_fail)
    
         
    # Execute all testsets
    if(tests[len(tests)-1].config.deferred == False):
        failures = run_testsets(tests)
        sys.exit(failures)


def parse_command_line_args(args_in):
    
    """ Runs everything needed to execute from the command line, so main method is callable without arg parsing """
    parser = OptionParser(
        usage="usage: %prog base_url test_filename.yaml [options] ")
    parser.add_option(u"--print-bodies", help="Print all response bodies",
                      action="store", type="string", dest="print_bodies")
    parser.add_option(u"--print-headers", help="Print all response headers",
                      action="store", type="string", dest="print_headers")
    parser.add_option(u"--log", help="Logging level",
                      action="store", type="string")
    parser.add_option(u"-I", help="folder path for input files",
                      action="store", type="string")
    parser.add_option(u"--interactive", help="Interactive mode",
                      action="store", type="string")
    parser.add_option(
        u"--url", help="Base URL to run tests against", action="store", type="string")
    parser.add_option(u"--test", help="Test file to use",
                      action="store", type="string")
    parser.add_option(u'--import_extensions',
                      help='Extensions to import, separated by semicolons', action="store", type="string")
    parser.add_option(
        u'--vars', help='Variables to set, as a YAML dictionary', action="store", type="string")
    parser.add_option(u'--verbose', help='Put cURL into verbose mode for extra debugging power',
                      action='store_true', default=False, dest="verbose")
    parser.add_option(u'--ssl-insecure', help='Disable cURL host and peer cert verification',
                      action='store_true', default=False, dest="ssl_insecure")
    parser.add_option(u'--absolute-urls', help='Enable absolute URLs in tests instead of relative paths',
                      action="store_true", dest="absolute_urls")
    parser.add_option(u'--skip_term_colors', help='Turn off the output term colors',
                      action='store_true', default=False, dest="skip_term_colors")

    (args, unparsed_args) = parser.parse_args(args_in)
    args = vars(args)

    # Handle url/test as named, or, failing that, positional arguments
    if not args['url'] or not args['test']:
        if len(unparsed_args) == 2:
            args[u'url'] = unparsed_args[0]
            args[u'test'] = unparsed_args[1]
        elif len(unparsed_args) == 1 and args['url']:
            args['test'] = unparsed_args[0]
        elif len(unparsed_args) == 1 and args['test']:
            args['url'] = unparsed_args[0]
        else:
            parser.print_help()
            parser.error(
                "wrong number of arguments, need both url and test filename, either as 1st and 2nd parameters or via --url and --test")


    # So modules can be loaded from current folder
    #args['cwd'] = os.path.realpath(os.path.abspath(os.getcwd()))
    #args['cwd']=args_in['I']
    return args


def command_line_run(args_in):
    args = parse_command_line_args(args_in)
    main(args)

# Allow import into another module without executing the main method
if(__name__ == '__main__'):
    command_line_run(sys.argv[1:])
