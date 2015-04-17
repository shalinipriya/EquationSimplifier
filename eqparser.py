# -----------------------------------------------------------------------------
# A parser for simple algebraic equations using David Beazley's PLY.
#
# It is based on the calc.py example provided in the PLY-3.4 distribution.
#
# -----------------------------------------------------------------------------
from printingcolors import *
from utils import *
import math, random, sys, time, bisect, string

pretty_printing_colors = {
    'FLOAT'          : bcolors.CYAN,
    'INT'            : bcolors.BLUE,
    'VARIABLENAME'   : bcolors.YELLOW,
    'SYMBOL'         : bcolors.GREEN,
    'EQUALS'         : bcolors.WHITE,
    'BINARYOP'       : bcolors.WHITE,
    'UNARYOP'        : bcolors.RED,
    'UNARYFUNCTION'  : bcolors.MAGENTA,
    }

reserved = {
   'log'  : 'LOG',
   'ln'   : 'LN',
   'sqrt' : 'SQRT',
   'sin'  : 'SINE',
   'cos'  : 'COSINE',
   'tan'  : 'TAN'
               }

tokens = [
    'SYMBOL',
    'VARIABLENAME','INT','FLOAT',
    'PLUS','MINUS','TIMES','DIVIDE','EXPONENT','EQUALS',
    'LPAREN','RPAREN']  + list(reserved.values()) 

binops = {
    '+' : 'PLUS',
    '-' : 'MINUS',
    '*' : 'TIMES',
    '/' : 'DIVIDE',
    '^' : 'EXPONENT',
    }

inverseOper = [{'from':'+', 'to':'-'},{'from':'-', 'to':'+'},{'from':'*', 'to':'/'},{'from':'/', 'to':'*'}]

# Tokens

t_PLUS         = r'\+'
t_MINUS        = r'-'
t_TIMES        = r'\*'
t_DIVIDE       = r'/'
t_EXPONENT     = r'\^'
t_EQUALS       = r'='
t_LPAREN       = r'\('
t_RPAREN       = r'\)'
t_VARIABLENAME = r'[a-zA-Z_][a-zA-Z0-9_]*'

def t_SYMBOL(t):
    r'e|pi'
    return t

def t_ID(t):
   r'[a-zA-Z_][a-zA-Z_0-9]*'
   t.type = reserved.get(t.value,'VARIABLENAME')    # Check for reserved words
   return t

# Read in a float. This rule has to be done before the int rule.
def t_FLOAT(t):
    r'-?\d+\.\d*(e-?\d+)?'
    t.value = float(t.value)
    return t

def t_INT(t):
    r'\d+'
    t.value = int(t.value)
    return t


# Ignored characters
t_ignore = " \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")
    
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)
    
# Build the lexer
import ply.lex as lex
lex.lex()






class Problem(object):
    """The abstract class for a formal problem.  You should subclass
    this and implement the methods actions and result, and possibly
    __init__, goal_test, and path_cost. Then you will create instances
    of your subclass and solve them with the various search functions."""

    def __init__(self, initial, find, goal=None ):
        """The constructor specifies the initial state, and possibly a goal
        state, if there is a unique goal.  Your subclass's constructor can add
        other arguments."""
	#initial - parse tree/Node
        self.initial = repr(initial); self.goal = goal
	self.parseTreeState = initial
	self.find = find
	#self.initialState = parse(initialExp);

    def actions(self, state):
        """Return the actions that can be executed in the given
        state. The result would typically be a list, but if there are
        many actions, consider yielding them one at a time in an
        iterator, rather than building them all at once."""
	
	assoCommList = []
	evalList = []
	#find out the terms matching some regular exp (binop, n1, n2)
	evalList = state.parseTreeState.searchop();
	
	#associativity and Commutavity
	assoCommList=state.parseTreeState.assocomm();
	
	#inverse
	inverseList = state.parseTreeState.inverse(self.find);
	return evalList + assoCommList +inverseList
	
    def result(self, state, action):
        """Return the state that results from executing the given
        action in the given state. The action must be one of
        self.actions(state)."""
	#action : replace/change/inverse,node, node
	
	#Evaluation
	prob = copy.deepcopy(state);
	replaceState = action ['node2'];	
	if(action['act']== "_replace"):
		if (replaceState.leaf) =='+':
			res = (replaceState.children[0].leaf)+(replaceState.children[1].leaf);
		elif (replaceState.leaf) == '*':
			res = (replaceState.children[0].leaf)*(replaceState.children[1].leaf);
		elif (replaceState.leaf) == '-':
			res = (replaceState.children[0].leaf)-(replaceState.children[1].leaf);
		elif (replaceState.leaf) == '/':
			res = (replaceState.children[0].leaf)/(replaceState.children[1].leaf);
		elif (replaceState.leaf) == '^':
			res = pow((replaceState.children[0].leaf),(replaceState.children[1].leaf));
		#search for replace state in prob		
		replaceState = prob.parseTreeState.searchInTree(prob.parseTreeState,replaceState)
		replaceState.children = [ ];
		replaceState.leaf= res;
		replaceState.type = "INT"
	#assoComm
	elif action['act']=="assoComm" :
		if(replaceState.children[0].children):
			if(replaceState.children[0].children[0].type =="INT" and replaceState.children[0].children[1].type=="VARIABLENAME" and replaceState.children[1].type =="INT"):
				temp1=replaceState.children[1].leaf
				temp2=replaceState.children[0].children[1].leaf
				replaceState = prob.parseTreeState.searchInTree(prob.parseTreeState,replaceState)
				replaceState.children[1].type = "VARIABLENAME"
				replaceState.children[1].leaf =temp2
				replaceState.children[0].children[1].type ="INT"
				replaceState.children[0].children[1].leaf =temp1
			elif(replaceState.children[0].children[1].type =="INT" and replaceState.children[0].children[0].type=="VARIABLENAME" and replaceState.children[1].type =="INT"):
				temp1=replaceState.children[1].leaf
				temp2=replaceState.children[0].children[0].leaf
				replaceState = prob.parseTreeState.searchInTree(prob.parseTreeState,replaceState)
				replaceState.children[1].type = "VARIABLENAME"
				replaceState.children[1].leaf =temp2
				replaceState.children[0].children[0].type ="INT"
				replaceState.children[0].children[0].leaf =temp1
		elif(replaceState.children[1].children):
			if(replaceState.children[1].children[0].type =="INT" and replaceState.children[1].children[1].type=="VARIABLENAME" and replaceState.children[0].type =="INT"):
				temp1=replaceState.children[0].leaf
				temp2=replaceState.children[1].children[1].leaf
				replaceState = prob.parseTreeState.searchInTree(prob.parseTreeState,replaceState)
				replaceState.children[0].type = "VARIABLENAME"
				replaceState.children[0].leaf =temp2
				replaceState.children[1].children[1].type ="INT"
				replaceState.children[1].children[1].leaf =temp1
			elif(replaceState.children[1].children[1].type =="INT" and replaceState.children[1].children[0].type=="VARIABLENAME" and replaceState.children[0].type =="INT"):
				temp1=replaceState.children[0].leaf
				temp2=replaceState.children[1].children[0].leaf
				replaceState = prob.parseTreeState.searchInTree(prob.parseTreeState,replaceState)
				replaceState.children[0].type = "VARIABLENAME"
				replaceState.children[0].leaf =temp2
				replaceState.children[1].children[0].type ="INT"
				replaceState.children[1].children[0].leaf =temp1
			
	elif action['act']=="inverse" :
		replaceState = prob.parseTreeState.searchInTree(prob.parseTreeState,replaceState)
		varChild = replaceState.checkForVar(self.find)
		
		if(varChild == "left"):
			if(replaceState.children[0].leaf == '+'):
				lhs=replaceState.children[0].children[1]
				rhs=replaceState.children[1]				
				replaceState.children[0]=replaceState.children[0].children[0]
				if(lhs.type =="INT" or lhs.type =="FLOAT"):
					if( not replaceState.children[1].children):
						temp2=Node("INT",[],rhs.leaf)
						temp1=Node("INT",[],lhs.leaf)
						tempnode=Node("BINARYOP",[temp2,temp1],'-')
						replaceState.children[1] = tempnode
		elif(varChild =="right"):
			if(replaceState.children[0].leaf == '+'):
				lhs=replaceState.children[0].children[0]
				rhs=replaceState.children[1]
				if(lhs.type =="INT" or lhs.type =="FLOAT"):
					replaceState.children[0]=replaceState.children[0].children[1]				
					if( not replaceState.children[1].children):
						temp2=Node("INT",[],rhs.leaf)
						temp1=Node("INT",[],lhs.leaf)
						tempnode=Node("BINARYOP",[temp2,temp1],'-')
						replaceState.children[1] = tempnode				
	return prob;
	

    def goal_test(self, state, variable):
        """Return True if the state is a goal. The default method compares the
        state to self.goal, as specified in the constructor. Override this
        method if checking against a single self.goal is not enough."""
#	print "check goal" + repr(state.parseTreeState)	


	if state.parseTreeState.type == "EQUALS" and state.parseTreeState.children[0].leaf== variable and state.parseTreeState.children[1].type=="INT":
		return True;
	elif state.parseTreeState.type == "EQUALS" and state.parseTreeState.children[1].leaf== variable and state.parseTreeState.children[0].type=="INT":
		return True
	else:
		evalList = state.parseTreeState.searchop()
		assoCommList=state.parseTreeState.assocomm()
		if not assoCommList and not evalList and not state.parseTreeState.checkInverse(variable):
			return True
		"""else:
			print "oh no"""


    def path_cost(self, c, state1, action, state2):
        """Return the cost of a solution path that arrives at state2 from
        state1 via action, assuming cost c to get up to state1. If the problem
        is such that the path doesn't matter, this function will only look at
        state2.  If the path does matter, it will consider c and maybe state1
        and action. The default method costs 1 for every step in the path."""
	#find depth of variable
	d=state2.parseTreeState.depth(self.find,1);
	md=state2.parseTreeState.maxDepth();
	return md
	#return c + 1

    def value(self, state):
        """For optimization problems, each state has a value.  Hill-climbing
        and related algorithms try to maximize this value."""
        abstract






# Define a Node class in order to permit explicit construction of a parse tree
class Node:
    def __init__(self,type,children=None,leaf=None):
         self.type = type
         if children:
              self.children = children
         else:
              self.children = [ ]
         self.leaf = leaf
	 self.EvalList=[]
    
    def __str__(self):
        # Produce the Parse Tree in prefix form
        if ((self.type == "FLOAT") or
            (self.type == "INT") or 
            (self.type == "VARIABLENAME") or 
            (self.type == "SYMBOL")):
                return pretty_printing_colors[self.type] + str(self.leaf) + bcolors.ENDC

        if (self.type == "EQUALS") or (self.type == "BINARYOP"):
            if self.leaf is '^': 
                return str(self.children[0]) + pretty_printing_colors[self.type] + self.leaf + bcolors.ENDC + str(self.children[1])
            else:
                # space these binary operators out
                return str(self.children[0]) + pretty_printing_colors[self.type] + " " + self.leaf + " " + bcolors.ENDC + str(self.children[1])

        if (self.type == "UNARYOP"):
            return  pretty_printing_colors[self.type] + self.leaf + bcolors.ENDC + str(self.children)
        if (self.type == "UNARYFUNCTION"):
            return  pretty_printing_colors[self.type] + self.leaf + bcolors.ENDC + "(" + str(self.children) + ")"


    def searchop(self):
	#return "hello";	
	#TODO:add float
	evalList=[]
	if (self.type == "BINARYOP" and (self.children[0].type =="INT" or self.children[0].type =="FLOAT")and (self.children[1].type == "INT" or self.children[1].type == "FLOAT")):
		return [{'act': '_replace', 'node2': self}];
		
	else:
		if self.children:
			for child in self.children:
				tempList=child.searchop()
				if tempList:
					evalList=evalList+tempList
		else:
			return None
	return evalList;

    def checkAssoComm(self):
	if (self.children and self.type == self.children[0].type and self.leaf == self.children[0].leaf):
		if(self.children[0].children and (self.children[0].children[0].type =="VARIABLENAME" or self.children[0].children[1].type =="VARIABLENAME") and not self.children[1].children and self.children[1].type == "INT"):
			return True
		elif(self.children[0].children and (self.children[0].children[0].type =="VARIABLENAME" or self.children[0].children[1].type =="VARIABLENAME") and not self.children[1].children and self.children[1].type == "INT"):
			return True

    
    def assocomm(self):
	#left
	assoCommList = []
	if (self.checkAssoComm()):
		return [{'act': 'assoComm', 'node2': self}];
		 		
	else :
		if self.children:
			for child in self.children:
				tempList=child.assocomm();
				if tempList:
					assoCommList=assoCommList+tempList	
		else:
			return None
	return assoCommList
	
    def checkInverse(self, variable):
	if (self.children[0].leaf != variable) or (self.children[1].leaf != variable):
		return True

    def checkForVar(self, variable):
	if self.children[0].leaf ==variable:
		return "left"
	elif self.children[1].leaf == variable:
		return "right"
	else:
		return self.children[0].checkForVar(variable);
		return self.children[0].checkForVar(variable);

    def inverse(self, variable):
	#inverseList = []
	if self.checkInverse(variable):
		if (self.children[0].children and (self.children[1].type == "INT" or self.children[1].type == "FLOAT")):
			return [{'act': 'inverse', 'node2': self}];
	return []	 		
	

    def maxDepth(self):
	if self.children:	
		ldepth=self.children[0].maxDepth();
		rdepth=self.children[1].maxDepth();
		if ldepth>rdepth:
			return ldepth+1
		else:
			return rdepth+1
	return 0;

    def depth(self, variable, level):
	if(self.leaf==variable):
		return level;
	else:
		for child in self.children:
			d=child.depth(variable, level+1);
		
		
	

    def searchInTree(self,node1, node2):
	if node1.type==node2.type and node1.children[0].leaf == node2.children[0].leaf and node1.children[1].leaf == node2.children[1].leaf:
		return node1;
	else:
		for child in node1.children:
			ret=self.searchInTree(child,node2)
			if ret:	
				return ret
	return None
    
    def __repr__(self):
        # Produce the Parse Tree in prefix form
        if ((self.type == "FLOAT") or
            (self.type == "INT") or 
            (self.type == "VARIABLENAME") or 
            (self.type == "SYMBOL")):
                return pretty_printing_colors[self.type] + str(self.leaf) + bcolors.ENDC

        s = "(" + pretty_printing_colors[self.type] 
        if (self.type == "EQUALS"):
            s+="=" + bcolors.ENDC 
        elif (self.type == "BINARYOP"):
            s+=self.leaf + bcolors.ENDC 
        elif (self.type == "UNARYOP"):
            s+=self.leaf + bcolors.ENDC 
        elif (self.type == "UNARYFUNCTION"):
            s+=self.leaf + bcolors.ENDC 

        s+=" "
        if type(self.children) is list:
            for child in self.children:
                s+=repr(child)
                s+=" "
            s = s[0:-1] # Gobble the extra space
        else:
                s+=repr(self.children)

        s +=  ")"
        return s

	
# Precedence rules for the arithmetic operators
precedence = (
    ('left','PLUS','MINUS'),
    ('left','TIMES','DIVIDE'),
    ('right','UMINUS'),
    ('left','EXPONENT'),
    )

def p_statement_assign(p):
    'statement : expression EQUALS expression'
    p[0] = Node('EQUALS', [p[1], p[3]], '=')

# We only allow equations, if we were to uncomment this, we'd parse algebraic expressions more generally
#def p_statement_expr(p):
#    'statement : expression'
#    p[0] = p[1] 

def p_expression_binop(p):
    '''expression : expression PLUS expression
                  | expression MINUS expression
                  | expression TIMES expression
                  | expression DIVIDE expression
                  | expression EXPONENT expression'''
    p[0] = Node('BINARYOP', [p[1], p[3]], p[2])

def p_expression_uminus(p):
    'expression : MINUS expression %prec UMINUS'
    p[0] = Node('UNARYOP', p[2], p[1])

def p_expression_single_fun(p):
    '''expression : LOG LPAREN expression RPAREN
                  | LN LPAREN expression RPAREN
                  | SQRT LPAREN expression RPAREN
                  | SINE LPAREN expression RPAREN
                  | COSINE LPAREN expression RPAREN
                  | TAN LPAREN expression RPAREN'''
    p[0] = Node('UNARYFUNCTION', p[3], p[1])

def p_expression_group(p):
    'expression : LPAREN expression RPAREN'
    p[0] = p[2]

def p_expression_float(p):
    'expression : FLOAT'
    p[0] = Node('FLOAT', [], p[1])

def p_expression_int(p):
    'expression : INT'
    p[0] = Node('INT', [], p[1])

def p_expression_name(p):
    'expression : VARIABLENAME'
    p[0] = Node('VARIABLENAME', [], p[1])

def p_expression_symbol(p):
    'expression : SYMBOL'
    p[0] = Node('SYMBOL', [], p[1])

def p_error(p):
    try:
        print("Syntax error at '%s'" % p.value)
    except:  
        print("Syntax error. An equation is expected.")

import ply.yacc as yacc
yacc.yacc()

def parse(s):
    return yacc.parse(s)

class SearchNode:
    """A node in a search tree. Contains a pointer to the parent (the node
    that this is a successor of) and to the actual state for this node. Note
    that if a state is arrived at by two paths, then there are two nodes with
    the same state.  Also includes the action that got us to this state, and
    the total path_cost (also known as g) to reach the node.  Other functions
    may add an f and h value; see best_first_graph_search and astar_search for
    an explanation of how the f and h values are handled. You will not need to
    subclass this class."""

    def __init__(self, state, parent=None, action=None, path_cost=0):
        "Create a search tree Node, derived from a parent by an action."
        update(self, state=state, parent=parent, action=action,
               path_cost=path_cost, depth=0)
        if parent:
            self.depth = parent.depth + 1

    def __repr__(self):
	return "<Node %s>" % (self.state,)

    def expand(self, problem):
        "List the nodes reachable in one step from this node."
        return [self.child_node(problem, action)
                for action in problem.actions(self.state)]

    def child_node(self, problem, action):
        "Fig. 3.10"
        next = problem.result(self.state, action)
        return SearchNode(next, self, action,
                    problem.path_cost(self.path_cost, self.state, action, next))

    def solution(self):
        "Return the sequence of actions to go from the root to this node."
        return [node.action for node in self.path()[1:]]

    def path(self):
        "Return a list of nodes forming the path from the root to this node."
        node, path_back = self, []
        while node:
            path_back.append(node)
            node = node.parent
        return list(reversed(path_back))

    # We want for a queue of nodes in breadth_first_search or
    # astar_search to have no duplicated states, so we treat nodes
    # with the same state as equal. [Problem: this may not be what you
    # want in other contexts.]

    def __eq__(self, other):
        return isinstance(other, Node) and self.state == other.state

    def __hash__(self):
        return hash(self.state)


def best_first_graph_search(problem, f):
    """Search the nodes with the lowest f scores first.
    You specify the function f(node) that you want to minimize; for example,
    if f is a heuristic estimate to the goal, then we have greedy best
    first search; if f is node.depth then we have breadth-first search.
    There is a subtlety: the line "f = memoize(f, 'f')" means that the f
    values will be cached on the nodes as they are computed. So after doing
    a best first search you can examine the f values of the path returned."""
    f = memoize(f, 'f')
    node = SearchNode(problem)

    if problem.goal_test(node.state, problem.find):
        return node
    frontier = PriorityQueue(min, f)
    frontier.append(node)
    explored = set()
    while frontier:
        node = frontier.pop()
        if problem.goal_test(node.state, problem.find):
            return node
        explored.add(node.state)

        for child in node.expand(problem):
            if child.state not in explored and child not in frontier:
                frontier.append(child)
            elif child in frontier:
                incumbent = frontier[child]
                if f(child) < f(incumbent):
                    del frontier[incumbent]
                    frontier.append(child)
    return None

