import string
import os
import copy
import json
import pycurl
import sys
import contenthandling
from contenthandling import ContentHandler
import validators
import parsing
from parsing import *
if PYTHON_MAJOR_VERSION > 2:
    import urllib.parse as urlparse
    from past.builtins import basestring
else:
    import urlparse


# Find the best implementation available on this platform
try:
    from cStringIO import StringIO as MyIO
except:
    try:
        from StringIO import StringIO as MyIO
    except ImportError:
        from io import BytesIO as MyIO

# Python 2/3 switches
PYTHON_MAJOR_VERSION = sys.version_info[0]
if PYTHON_MAJOR_VERSION > 2:
    import urllib.parse as urlparse
    from past.builtins import basestring
else:
    import urlparse

# Python 3 compatibility shims
import six
from six import binary_type
from six import text_type
from six import iteritems
from six.moves import filter as ifilter

"""
Pull out the Test objects and logic associated with them
This module implements the internal responsibilities of a test object:
- Test parameter/configuration storage
- Templating for tests
- Parsing of test configuration from results of YAML read
"""

BASECURL = pycurl.Curl()  # Used for some validation/parsing

DEFAULT_TIMEOUT = 10  # Seconds


# Parsing helper functions
def coerce_to_string(val):
    if isinstance(val, text_type):
        return val
    elif isinstance(val, int):
        return text_type(val)
    elif isinstance(val, binary_type):
        return val.decode('utf-8')
    else:
        raise TypeError("Input {0} is not a string or integer, and it needs to be!".format(val))

def coerce_string_to_ascii(val):
    if isinstance(val, text_type):
        return val.encode('ascii')
    elif isinstance(val, binary_type):
        return val
    else:
        raise TypeError("Input {0} is not a string, string expected".format(val))


def coerce_list_of_strings(val):
    """ If single value, try to parse as string, else try to parse as list of string """
    if isinstance(val, list):
        return [x for x in val]
    else:
        return [val]




class WorkFlow(object):
    name = u'Unnamed'
    tests=[] 
    templates = None  # Dictionary of template to compiled template

    # Bind variables, generators, and contexts
    variable_binds = None
    generator_binds = None  # Dict of variable name and then generator name
    extract_binds = None  # Dict of variable name and extract function to run
    params=None
    params_templated=None


    @staticmethod
    def has_contains():
        return 'contains' in validators.VALIDATORS

    def ninja_copy(self):
        """ Optimization: limited copy of test object, for realize() methods
            This only copies fields changed vs. class, and keeps methods the same
        """
        output = Test()
        myvars = vars(self)
        output.__dict__ = myvars.copy()
        return output

    
    def del_template(self, variable_name):
        """ Remove template instance, so we no longer use one for this test """
        if self.templates is not None and variable_name in self.templates:
            del self.templates[variable_name]

    def realize_template(self, variable_name, context):
        """ Realize a templated value, using variables from context
            Returns None if no template is set for that variable """
        val = None
        if context is None or self.templates is None or variable_name not in self.templates:
            return None
        return self.templates[variable_name].safe_substitute(context.get_values())



    def update_context_before(self, context):
        """ Make pre-test context updates, by applying variable and generator updates """
        if self.variable_binds:
            context.bind_variables(self.variable_binds)
        if self.generator_binds:
            for key, value in self.generator_binds.items():
                context.bind_generator_next(key, value)

    def update_context_after(self, response_body, headers, context):
        """ Run the extraction routines to update variables based on HTTP response body """
        if self.extract_binds:
            for key, value in self.extract_binds.items():
                result = value.extract(
                    body=response_body, headers=headers, context=context)
                context.bind_variable(key, result)

    def is_context_modifier(self):
        """ Returns true if context can be modified by this test
            (disallows caching of templated test bodies) """
        return self.variable_binds or self.generator_binds or self.extract_binds

    def is_dynamic(self):
        """ Returns true if this test does templating """
        if self.templates:
            return True
        elif isinstance(self._body, ContentHandler) and self._body.is_dynamic():
            return True
        return False

    def realize(self, context=None):
        """ Return a fully-templated test object, for configuring curl
            Warning: this is a SHALLOW copy, mutation of fields will cause problems!
            Can accept a None context """
      
        if not self.is_dynamic() or context is None:
            return self
        else:
            selfcopy = self.ninja_copy()
          
            if(selfcopy.params):
                pass    
            selfcopy.templates = None
           # if isinstance(self._body, ContentHandler):
           #     selfcopy.params = self._params.get_content(context)
            selfcopy.params = self.get_params(context=context)
            return selfcopy

    def realize_partial(self, context=None):
        """ Attempt to template out what is static if possible, and load files.
            Used for performance optimization, in cases where a test is re-run repeatedly
            WITH THE SAME Context.
        """

        if self.is_context_modifier():
            # Don't template what is changing
            return self
        elif self.is_dynamic():  # Dynamic but doesn't modify context, template everything
            return self.realize(context=context)

        # See if body can be replaced
        para = self._params
        newpara = None
        if para and isinstance(para, ContentHandler) and para.is_file and not para.is_template_path:
            # File can be UN-lazy loaded
            newpara = para.create_noread_version()

        output = self
        if newpara:  # Read body
            output = copy.copy(self)
            output.params = newpara
        return output

    def __init__(self):
        #self.headers = dict()
        #self.expected_status = [200]
        self.templated = dict()
               
  
    def __str__(self):
        return json.dumps(self, default=safe_to_json)

    def setvalue_body(self, value,list_params):
        """ Set body, directly """

        body_dict=dict()
        body_dict["body"]=value
        list_params.append(body_dict)

        self._body = value
        

    def get_body(self, context=None):
        """ Read body from file, applying template if pertinent """
        
        if self._body is None:
            return None
        elif isinstance(self._body, basestring):
            return self._body
        else:
            return self._body.get_content(context=context)

    body = property(get_body, setvalue_body, None,
                    'Request body, if any (for POST/PUT methods)')



    def setvalue_auth_password(self, value,list_params,isTemplate=False):
        """ Set Auth Password, passing flag if using a template """
        pass_dict=dict()
        
        if isTemplate:
            self.set_template(self.NAME_AUTH_PASSWORD, value)
        else:
            self.del_template(self.NAME_AUTH_PASSWORD)
        pass_dict["auth_password"]=value
        list_params.append(pass_dict) 
        self._auth_password = value

 
    NAME_AUTH_PASSWORD = 'auth_password'
    auth_password = property(setvalue_auth_password, None, 'Auth Password')
     
    def setvalue_auth_username(self, value,list_params,isTemplate=False):
        """ Set Auth Username, passing flag if using a template """
        pass_dict=dict()
        
        if isTemplate:
            self.set_template(self.NAME_AUTH_USERNAME, value)
        else:
            self.del_template(self.NAME_AUTH_USERNAME)
        pass_dict["auth_username"]=value
        list_params.append(pass_dict) 
        self._auth_username = value

 
    NAME_AUTH_USERNAME = 'auth_username'
    auth_username = property(setvalue_auth_username, None, 'Auth username')

    def setvalue_url(self, value,list_params,isTemplate=False):
        """ Set URL, passing flag if using a template """
        
        pass_dict=dict()
        if isTemplate:
            self.set_template(self.NAME_URL, value)
        else:
            self.del_template(self.NAME_URL)
        pass_dict["url"]=value
        list_params.append(pass_dict) 
        self._url = value

    
    NAME_URL = 'url'
    url = property(setvalue_url, None, 'URL fragment for request')
    
    def setvalue_method(self, value,list_params,isTemplate=False):
        """ Set method, passing flag if using a template """
        
        pass_dict=dict()
        if isTemplate:
            self.set_template(self.NAME_METHOD, value)
        else:
            self.del_template(self.NAME_METHOD)
        pass_dict["method"]=value
        list_params.append(pass_dict) 
        self._method = value
 
    NAME_METHOD = 'method'
    method = property(setvalue_method, None, 'Method type for request')
     

    def setvalue_expected_status(self, value,list_params,isTemplate=False):
        """ Set expected_status, passing flag if using a template """
        
        pass_dict=dict()
        if isTemplate:
            self.set_template(self.NAME_EXPECTED_STATUS, value)
        else:
            self.del_template(self.NAME_EXPECTED_STATUS)
        pass_dict["expected_status"]=value
        list_params.append(pass_dict) 
        self._expected_status = value
 
    NAME_EXPECTED_STATUS = 'expected_status'
    expected_status = property(setvalue_expected_status, None, 'expected status')


    def setvalue_headers(self,value,list_params,isTemplate=False):
        """ Set headers, passing flag if using a template """
        headers_dict=dict()
        if isTemplate:
            self.set_template(self.NAME_HEADERS, 'Dict_Templated')
        else:
            self.del_template(self.NAME_HEADERS)
        headers_dict["headers"]=value
        list_params.append(headers_dict) 
        self._headers = value

    
    NAME_HEADERS = 'headers'
    # Totally different from others

    headers = property(setvalue_headers, None,
                       'Headers dictionary for request')
    

    def set_template(self, variable_name, template_string):
        """ Add a templating instance for variable given """
        
        if self.templates is None:
            self.templates = dict()
        self.templates[variable_name] = string.Template(template_string)
        

  

    @classmethod
    def parse_workflow(cls, base_url,node,input_workflow=None, test_path=None , global_gen=None):
        
        myworkflow = input_workflow
        if not myworkflow:
            myworkflow = WorkFlow()

        # Clean up for easy parsing
        node = lowercase_keys(flatten_dictionaries(node))
       


        # Simple table of variable name, coerce function, and optionally special store function
        CONFIG_ELEMENTS = {
            # Simple variables
            u'name': [coerce_string_to_ascii],
            u'tests': [coerce_list_of_strings],
            u'body': [ContentHandler.parse_content],
            u'group': [coerce_to_string] # Test group name
           
        }

        def use_config_parser(configobject, configelement, configvalue):
            """ Try to use parser bindings to find an option for parsing and storing config element
                :configobject: Object to store configuration
                :configelement: Configuratione element name
                :configvalue: Value to use to set configuration
                :returns: True if found match for config element, False if didn't
            """
            
            myparsing = CONFIG_ELEMENTS.get(configelement)
            if myparsing:
                converted = myparsing[0](configvalue)
                setattr(configobject, configelement, converted)
                return True
            return False
       
        """Fuction mapping"""
        functions_case={'setvalue_body':[WorkFlow.setvalue_body],'setvalue_headers':[WorkFlow.setvalue_headers],'setvalue_auth_password':[WorkFlow.setvalue_auth_password],'setvalue_auth_username':        				 [WorkFlow.setvalue_auth_username],'setvalue_url':[WorkFlow.setvalue_url],'setvalue_method':[WorkFlow.setvalue_method],'setvalue_expected_status':[WorkFlow.setvalue_expected_status]}
        
        # Copy/convert input elements into appropriate form for a test object
        for configelement, configvalue in node.items():
            
            if use_config_parser(myworkflow, configelement, configvalue):
                continue
          
            elif configelement == u'name':
                myworkflow.name = str(configvalue)
         
           
            elif configelement == u'extract_binds':
                # Add a list of extractors, of format:
                # {variable_name: {extractor_type: extractor_config}, ... }
                binds = flatten_dictionaries(configvalue)
                if myworkflow.extract_binds is None:
                    myworkflow.extract_binds = dict()
                
                for variable_name, extractor in binds.items():
                    if not isinstance(extractor, dict) or len(extractor) == 0:
                        raise TypeError(
                            "Extractors must be defined as maps of extractorType:{configs} with 1 entry")
                    if len(extractor) > 1:
                        raise ValueError(
                            "Cannot define multiple extractors for given variable name")

                    # Safe because length can only be 1
                    for extractor_type, extractor_config in extractor.items():
                        myworkflow.extract_binds[variable_name] = validators.parse_extractor(extractor_type, extractor_config)
                        mytest.variable_binds= validators.parse_extractor(extractor_type, extractor_config)
            
           

            elif configelement == u'params':
                params_flag=1
                dict_params=dict()
                dict_templated_params=dict()
                for p in range(len(configvalue)):
                    for key1,value1 in configvalue[p].items():
                        list_params=list()
                        list_templated_params=list()
                        for q in range(len(value1)):                            
                            for key2,value2 in value1[q].items():
				
                                if(key2 == "name"):
        			    raise Exception("Cannot overwrite name attribute of original test case")

    				if(key2 == "group"):
        			    raise Exception("Cannot overwrite group attribute of original test case")	               

                                if(key2=="body"):
                                    assert isinstance(value2, dict)
                                    myparsing = CONFIG_ELEMENTS.get(key2)
                                    converted = myparsing[0](value2)
                                    myworkflow.setvalue_body(converted,list_params)
                                    continue

 				if(key2=="generator_binds"):
 				    assert isinstance(value2, dict)
		                    atrr_dict=dict()
                                    atrr_dict[key2]=value2
    		                    list_params.append(atrr_dict)
                                    continue

				if(key2=="delay" or key2 == "retries" or key2 == "repeat"):
                                    assert isinstance(value2, int)
		                    atrr_dict=dict()
                                    atrr_dict[key2]=value2
    		                    list_params.append(atrr_dict)
                                    continue
                                  
				if(key2=="extract_binds"):
                                   
                                    temp_dict=dict()
		                    atrr_dict=dict()
                                    for index in range(len(value2)):
                                        for variable_name, extractor in value2[index].items():
                                            if not isinstance(extractor, dict) or len(extractor) == 0:
                                                raise TypeError(
                                                            "Extractors must be defined as maps of extractorType:{configs} with 1 entry")
                                            if len(extractor) > 1:
                                                raise ValueError(
                                                             "Cannot define multiple extractors for given variable name")

                                       	    # Safe because length can only be 1
                                            for extractor_type, extractor_config in extractor.items():
                                                temp_dict[variable_name] = validators.parse_extractor(extractor_type, extractor_config)

                                            atrr_dict[key2]=temp_dict
    		                            list_params.append(atrr_dict)
                                            continue                                

                                var_func="setvalue_"+key2

                                if isinstance(value2, dict):
                                    output = flatten_dictionaries(value2)
                                else:
                                    output = value2
                                #output={'template': {'license': {'name': 'randhir', 'properties': '$var22'}}}
		                if isinstance(output, dict):
		                    filterfunc  = lambda x: str(x[0]).lower() == 'template'  # Templated items
		                    templates = [x for x in ifilter(filterfunc, output.items())]#output_items=[('template', {'license': {'name': 'randhir', 'properties': '$var22'}})]
		                else:
		                    templates = None
                                
                                
		                if templates:
                                    list_templated_params.append(key2)
   
                                    if(var_func=='setvalue_auth_username'):    
                                        functions_case[var_func][0](myworkflow,templates[0][1],list_params,isTemplate=True)
                                    if(var_func=='setvalue_auth_password'):    
                                        functions_case[var_func][0](myworkflow,templates[0][1],list_params,isTemplate=True)
                                    if(var_func=='setvalue_headers'):
                                        functions_case[var_func][0](myworkflow,templates[0][1],list_params,isTemplate=True)
				    if(var_func=='setvalue_url'):
                                        temp=urlparse.urljoin(base_url,coerce_to_string(templates[0][1]))
                                        functions_case[var_func][0](myworkflow,temp,list_params,isTemplate=True)
                                    if(var_func=='setvalue_method'):
                                        functions_case[var_func][0](myworkflow,templates[0][1],list_params,isTemplate=True)
                                    if(var_func=='setvalue_expected_status'):
                                        functions_case[var_func][0](myworkflow,templates[0][1],list_params,isTemplate=True)

                                else: 
                                    
                                    if(var_func=='setvalue_auth_username'):    
                                        functions_case[var_func][0](myworkflow,output,list_params)
                                    if(var_func=='setvalue_auth_password'):    
                                        functions_case[var_func][0](myworkflow,output,list_params)
                                    if(var_func=='setvalue_headers'):
                                        functions_case[var_func][0](myworkflow,output,list_params)
				    if(var_func=='setvalue_url'):
                                        temp=urlparse.urljoin(base_url,coerce_to_string(output))
                                        functions_case[var_func][0](myworkflow,temp,list_params)
                                    if(var_func=='setvalue_method'):
                                        functions_case[var_func][0](myworkflow,output,list_params)
                                    if(var_func=='setvalue_expected_status'):
                                        functions_case[var_func][0](myworkflow,output,list_params)


		                
		                
                        dict_params[str(key1)]=list_params
                        dict_templated_params[str(key1)]=list_templated_params
                myworkflow.params=dict_params
                myworkflow.params_templated=dict_templated_params
  
            elif configelement == 'variable_binds':
                myworkflow.variable_binds = flatten_dictionaries(configvalue)
           
        return myworkflow
