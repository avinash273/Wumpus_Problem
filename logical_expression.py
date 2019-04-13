#!/usr/bin/env python

#-------------------------------------------------------------------------------
# Name:        logical_expression
# Purpose:     Contains logical_expression class, inference engine,
#              and assorted functions
#
# Created:     09/25/2011
# Last Edited: 07/22/2013  
# Notes:       *This contains code ported by Christopher Conly from C++ code
#               provided by Dr. Vassilis Athitsos
#              *Several integer and string variables are put into lists. This is
#               to make them mutable so each recursive call to a function can
#               alter the same variable instead of a copy. Python won't let us
#               pass the address of the variables, so put it in a list which is
#               passed by reference. We can also now pass just one variable in
#               the class and the function will modify the class instead of a
#               copy of that variable. So, be sure to pass the entire list to a
#               function (i.e. if we have an instance of logical_expression
#               called le, we'd call foo(le.symbol,...). If foo needs to modify
#               le.symbol, it will need to index it (i.e. le.symbol[0]) so that
#               the change will persist.
#              *Written to be Python 2.4 compliant for omega.uta.edu
#-------------------------------------------------------------------------------

# Logic Modified by Avinash Shanker
# AXS8570
# 1001668570
# This is a driver program
# Usage: python check_true_false.py wumpus_rules.txt additional_knowledge.txt statement.txt
# My Logic starts from mentioned below...

import sys
from copy import copy

#-------------------------------------------------------------------------------
# Begin code that is ported from code provided by Dr. Athitsos
class logical_expression:
    """A logical statement/sentence/expression class"""
    # All types need to be mutable, so we don't have to pass in the whole class.
    # We can just pass, for example, the symbol variable to a function, and the
    # function's changes will actually alter the class variable. Thus, lists.
    def __init__(self):
        self.symbol = ['']
        self.connective = ['']
        self.subexpressions = []



def print_expression(expression, separator):
    """Prints the given expression using the given separator"""
    if expression == 0 or expression == None or expression == '':
        print '\nINVALID\n'

    elif expression.symbol[0]: # If it is a base case (symbol)
        sys.stdout.write('%s' % expression.symbol[0])

    else: # Otherwise it is a subexpression
        sys.stdout.write('(%s' % expression.connective[0])
        for subexpression in expression.subexpressions:
            sys.stdout.write(' ')
            print_expression(subexpression, '')
            sys.stdout.write('%s' % separator)
        sys.stdout.write(')')


def read_expression(input_string, counter=[0]):
    """Reads the next logical expression in input_string"""
    # Note: counter is a list because it needs to be a mutable object so the
    # recursive calls can change it, since we can't pass the address in Python.
    
    result = logical_expression()
    length = len(input_string)
    while True:
        if counter[0] >= length:
            break

        if input_string[counter[0]] == ' ':    # Skip whitespace
            counter[0] += 1
            continue

        elif input_string[counter[0]] == '(':  # It's the beginning of a connective
            counter[0] += 1
            read_word(input_string, counter, result.connective)
            read_subexpressions(input_string, counter, result.subexpressions)
            break

        else:  # It is a word
            read_word(input_string, counter, result.symbol)
            break
    return result


def read_subexpressions(input_string, counter, subexpressions):
    """Reads a subexpression from input_string"""
    length = len(input_string)
    while True:
        if counter[0] >= length:
            print '\nUnexpected end of input.\n'
            return 0

        if input_string[counter[0]] == ' ':     # Skip whitespace
            counter[0] += 1
            continue

        if input_string[counter[0]] == ')':     # We are done
            counter[0] += 1
            return 1

        else:
            expression = read_expression(input_string, counter)
            subexpressions.append(expression)


def read_word(input_string, counter, target):
    """Reads the next word of an input string and stores it in target"""
    word = ''
    while True:
        if counter[0] >= len(input_string):
            break

        if input_string[counter[0]].isalnum() or input_string[counter[0]] == '_':
            target[0] += input_string[counter[0]]
            counter[0] += 1

        elif input_string[counter[0]] == ')' or input_string[counter[0]] == ' ':
            break

        else:
            print('Unexpected character %s.' % input_string[counter[0]])
            sys.exit(1)


def valid_expression(expression):
    """Determines if the given expression is valid according to our rules"""
    if expression.symbol[0]:
        return valid_symbol(expression.symbol[0])

    if expression.connective[0].lower() == 'if' or expression.connective[0].lower() == 'iff':
        if len(expression.subexpressions) != 2:
            print('Error: connective "%s" with %d arguments.' %
                        (expression.connective[0], len(expression.subexpressions)))
            return 0

    elif expression.connective[0].lower() == 'not':
        if len(expression.subexpressions) != 1:
            print('Error: connective "%s" with %d arguments.' %
                        (expression.connective[0], len(expression.subexpressions)))
            return 0

    elif expression.connective[0].lower() != 'and' and \
         expression.connective[0].lower() != 'or' and \
         expression.connective[0].lower() != 'xor':
        print('Error: unknown connective %s.' % expression.connective[0])
        return 0

    for subexpression in expression.subexpressions:
        if not valid_expression(subexpression):
            return 0
    return 1


def valid_symbol(symbol):
    """Returns whether the given symbol is valid according to our rules."""
    if not symbol:
        return 0

    for s in symbol:
        if not s.isalnum() and s != '_':
            return 0
    return 1

# End of ported code
#-------------------------------------------------------------------------------

#Avinash code Starts Here
        
def extend(format, symb, value):
    format[symb] = value
    return format

#Functions assists in forming Regular expression
def Get_Expression(expression, symbols):
    if expression.symbol[0]:
        symbols.append(expression.symbol[0])
    for subexpression in expression.subexpressions:
        Get_Expression(subexpression, symbols)


#Function to perform check of TT_Entails for each statement
def Func_Check_Entails(kb, alpha, symbols, format):
    if not symbols:
        if Get_PL_Exp_State(kb, format):
            return Get_PL_Exp_State(alpha, format)
        else:
            return True
    p = symbols[0]
    rest = symbols[1:]
    return Func_Check_Entails( kb, alpha, rest, extend(format, p, True) ) \
           and Func_Check_Entails( kb, alpha, rest, extend(format, p, False) )


#Function to check if the PL statement is true for collectives and each symbol
def Get_PL_Exp_State(expression, format):
    if expression.connective[0].lower() == 'and':
        state = True
        for i, subexpression in enumerate(expression.subexpressions):
            if(i == 0):
                state = Get_PL_Exp_State(subexpression, format)
                continue;
            state = state and Get_PL_Exp_State(subexpression, format)
        return state
    elif expression.connective[0].lower() == 'or':
        state = True
        for i, subexpression in enumerate(expression.subexpressions):
            if(i == 0):
                state = Get_PL_Exp_State(subexpression, format)
                continue;
            state = state or Get_PL_Exp_State(subexpression, format)
        return state
    elif expression.connective[0].lower() == 'not':
        state = not Get_PL_Exp_State(expression.subexpressions[0], format)
        return state
    elif expression.connective[0].lower() == 'xor':
        state = True
        for i, subexpression in enumerate(expression.subexpressions):
            if(i == 0):
                state = Get_PL_Exp_State(subexpression, format)
                continue;
            state = state ^ Get_PL_Exp_State(subexpression, format)
        return state
    elif expression.connective[0].lower() == 'if':
        exp1 = Get_PL_Exp_State(expression.subexpressions[0], format)
        exp2 = Get_PL_Exp_State(expression.subexpressions[1], format)
        return ( (not exp1) or exp2 )
    elif expression.connective[0].lower() == 'iff':
        exp1 = Get_PL_Exp_State(expression.subexpressions[0], format)
        exp2 = Get_PL_Exp_State(expression.subexpressions[1], format)
        return ( (not exp1) or exp2 ) and ( (not exp2) or exp1 )
    return format[expression.symbol[0]]

#Function performs task of TT_Entails to check synbols and statements with my Knowledge Base
def Fun_TT_Entails(knowledge_base, statement, negation, symlist):
    
    try:
        Result = open('result.txt', 'w')
    except:
        print('Unable to Create Output File')
    Temp_Knowledge_Base = []
    Temp_Symbol = []
    format = symlist.copy(); 
    Get_Expression(knowledge_base, Temp_Knowledge_Base)
    Get_Expression(statement, Temp_Symbol)
    Temp_Knowledge_Base = list(set(Temp_Knowledge_Base))
    Temp_Symbol = list(set(Temp_Symbol))
    Temp_Knowledge_Base.extend(Temp_Symbol)
    symbols = list(set(Temp_Knowledge_Base))
    for symb in format.keys():
        try:
            symbols.remove(symb)
        except Exception:
            pass
    True_Statement = Func_Check_Entails(knowledge_base, statement, symbols, format)
    Negation_Statement = Func_Check_Entails(knowledge_base, negation, symbols, format)
    if True_Statement == True and Negation_Statement == False:
        Result.write('Statement Definitely True') 
        print 'Statement Definitely True'
    elif True_Statement == False and Negation_Statement == True:
        Result.write('Statement Definitely False')
        print 'Statement Definitely False'
    elif True_Statement == False and Negation_Statement == False:
        Result.write('Statement Possibly True or Possibly False')
        print 'Statement Possibly True or Possibly False'
    elif True_Statement == True and Negation_Statement == True:
        Result.write('Statement Both True & False')
        print 'Both True & False'
    else:
        Result.write('Invalid Statement or KB, Please try with different Input')    
    print
    Result.close()
