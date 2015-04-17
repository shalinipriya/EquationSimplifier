#!/usr/bin/python
import eqparser 

while 1:
    try:
        s = raw_input('eq > ')   # use input() on Python 3
	variable = raw_input('var > ')
    except EOFError:
        print
        break
  
    p = eqparser.parse(s)
    print "This is parsed at: " + repr(p)
    prob=eqparser.Problem(p, variable);
    sol =eqparser.best_first_graph_search(prob, lambda node: node.path_cost);
    print "Solution: " + str(sol.state.parseTreeState)
    """while (not(prob.goal_test(prob, variable))):	
    	prob = prob.actions(prob);
    	#p2 = prob.actions(p1);	
    	print "In infix form: " + str(prob.parseTreeState)	"""
    #print "This is parsed at: " + repr(p1)
    
    #x=p.searchop();
    #p.assocomm();
    #print "This is parsed at: " + repr(x)



