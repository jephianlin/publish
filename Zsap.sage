### VariationsOfZsap
### Author: Jephian Lin

### This file is copied from https://sage.math.iastate.edu/home/pub/54/
### which was cited by
### J. C.-H. Lin. Using a new zero forcing process to guarantee the Strong Arnold Property. Linear Algebra Appl., 507:229--250, 2016.

### Moved to Github and update the code for Python 3 on January, 2020.

### Tested under SageMath 9.0
### See the illustration file Zsap_illustration.ipynb on
### https://github.com/jephianlin/publish


###A random algorithm is implemented for finding the value of Zsap's.

import random #if this line is not included, then change random.choice to choice. 
       	
###Codes for all variations of Zsap.

def Z_game(g,B,ban=[]):
    """
    Input:
        g: a simple graph
        B: a set of initial blue vertices
        ban: a set of banned vertices
    Output:
        return the derived set under the regular CCR-Z.
        Note: vertices in ban cannot make a force, but are still white neighbors if white.
    """    
    V=g.vertices();
    white_neighbors={}; #a dictionary with the structure {v: list of white neighbors}
    white_numbers={}; #a dictionary with the structure {v: number of white neighbors}
    for v in V:
        nbh=g.neighbors(v);
        for b in B:
            try:
                nbh.remove(b);
            except ValueError:
                pass;
        white_neighbors[v]=nbh;
        white_numbers[v]=len(nbh);
    queue=copy(B); #queue stores list of vertices that can possibly make a force
    derived_set=copy(B); #derived_set stores the set of blue vertices
    whole_loop=True;
    while whole_loop: #keep searching if queue!=[]
        try:
            v=queue[0];
            queue.remove(v);
            if v not in ban and white_numbers[v]==1:
                u=white_neighbors[v][0]; #the only white neighbor
                derived_set.append(u); #make the force
                #update white_numbers, white_neighbors, and queue
                if white_numbers[u]==1: 
                    queue.append(u);
                u_nbr=g.neighbors(u);
                for w in u_nbr:
                    white_neighbors[w].remove(u);
                    white_numbers[w]+=-1;
                    if w in derived_set and white_numbers[w]==1:
                        queue.append(w);
        except IndexError:
            whole_loop=False;
    return derived_set;
    
def Zell_game(g,B,ban=[]): ##every non-isolated vertex can force itself if no other white neighbors.
    """
    Input:
        g: a simple graph
        B: a set of initial blue vertices
        ban: a set of banned vertices
    Output:
        return the derived set under the CCR-Zell.  
        That is, in addition to CCR-Z, every non-isolated vertex can force itself if 
        no other white neighbors.
        Note: vertices in ban cannot make a force, but are still white neighbors if white.
    """    
    #Build h from g by deleting all isolated vertices,
    # since they are not going to change the outcome. 
    h=g.copy();
    for v in g.vertices():
        if h.degree(v)==0:
            h.delete_vertex(v);
    V=h.vertices();
    white_neighbors={}; #a dictionary with the structure {v: list of white closed neighbors}
    white_numbers={}; #a dictionary with the structure {v: number of white closed neighbors}
    for v in V:
        nbh=h.neighbors(v);
        nbh.append(v);
        for b in B:
            try:
                nbh.remove(b);
            except ValueError:
                pass;
        white_neighbors[v]=nbh;
        white_numbers[v]=len(nbh);
    queue=copy(V); #queue stores list of vertices that can possibly make a force
    derived_set=copy(B); #derived_set stores the set of blue vertices
    whole_loop=True;
    while whole_loop: #keep searching if queue!=[]
        try:
            v=queue[0];
            queue.remove(v);
            if v not in ban and white_numbers[v]==1:
                u=white_neighbors[v][0]; #the only white neighbor
                derived_set.append(u); #make the force
                #update white_numbers, white_neighbors, and queue
                u_nbr=h.neighbors(u);
                u_nbr.append(u);
                for w in u_nbr:
                    white_neighbors[w].remove(u);
                    white_numbers[w]+=-1;
                    if white_numbers[w]==1:
                        queue.append(w);
        except IndexError:
            whole_loop=False;
    return derived_set;

def Zplus_game(g,B):
    """
    Input:
        g: a simple graph
        B: a set of initial blue vertices
    Output:
        return the derived set under the CCR-Zplus.  
        That is, apply CCR-Z to each white branch.
        Note: the banned set is not implemented, since Zvcoc has no Zplus version.
    """   
    white_graph=g.copy(); #recording the induced subgraph on white
    derived_set=copy(B); #derived_set stores the set of blue vertices
    for b in derived_set:
        white_graph.delete_vertex(b);
    whole_loop=True;
    while whole_loop: 
        whole_loop=False; #open again only when something found.
        whole_extra_B=[]; #extra blue vertices found in this round
        partition=white_graph.connected_components();
        for com in partition:
            considered_set=copy(com);
            for v in derived_set:
                considered_set.append(v);
            considered_graph=g.subgraph(considered_set); #this is a white branch
            extra_B=Z_game(considered_graph,derived_set); #apply Z_game to this white branch
            for v in derived_set:
                extra_B.remove(v);
            for v in extra_B:
                whole_loop=True; #something found, open whole_loop
                whole_extra_B.append(v);
        #update new derived_set and new white_graph.
        for v in whole_extra_B:
            derived_set.append(v);
            white_graph.delete_vertex(v);
    return derived_set;

def Zsap_game(g,B,rule="CCRZ",oc_rule=False,banned_dict={}): 
    """
    Input:
        g: a simple graph
        B: a set of initial blue non-edges
        rule: rule that appplies - "CCRZ", "CCRZell", or "CCRZplus"
        oc_rule: if the odd cycle rule applies - True or False
        banned_dict: a dictionary with structure {v: banned vertices in the local game l(g,v,rule)}
            **Usually called by find_Zsap when get_value="vertex".
    Output:
        return the derived set of the SAP zero forcing game through the CCRZsap^rule.  
    """   
    active={}; 
    #for each vertex i, assign a value of 1,0. 
    #1 means l(g,i) can possibly make a force, while 0 means that is impossible.
    V=g.vertices();
    for v in V:
        active[v]=1;
    #complete banned_dict by empty sets
    for v in V:  
        if v not in banned_dict.keys(): 
            banned_dict[v]=[];
    queue=[v for v in V] #vertices i such that its local game is still active
    derived_set=copy(B); #derived_set stores the set of blue non-edges
    #######
    #the whole_loop contains two sub-loops: regular_loop and oc_loop
    # regular_loop go make all possible forces without the odd cycle rule
    # oc_rule make all possible forces with only the odd cycle rule
    #whole_loop stops when nothing is found in both sub-loops
    #if oc_rule=False, then whole_loop will run only once.
    #######
    whole_loop=True;        
    while whole_loop: 
        whole_loop=False; #open again only when something found, either in regular_loop or oc_loop.
        regular_loop=True; 
        while regular_loop: 
            try:
                u=queue[0]; #starting from the second whloe loop, queue is given by oc loop.
                queue.remove(u);
                if active[u]==1:
                    #consider the local game l(g,u,rule)
                    #local_B contains all the neighbors of u, u itself, and all blue non-neighbor of u
                    #make all possible forces in this local game
                    local_B=g.neighbors(u);
                    local_B.append(u);
                    for v in V:
                        if (u,v) in derived_set or (v,u) in derived_set:
                            local_B.append(v);
                    if rule=="CCRZ":
                        extra_B=list(Z_game(g,local_B,banned_dict[u]));
                    if rule=="CCRZell":
                        extra_B=list(Zell_game(g,local_B,banned_dict[u]));
                    if rule=="CCRZplus":
                        extra_B=list(Zplus_game(g,local_B));
                    for v in local_B:
                        extra_B.remove(v);
                    for v in extra_B:
                        derived_set.append((u,v));
                        active[v]=1;
                        queue.append(v);
                        whole_loop=True; #something found, open whole_loop
                active[u]=0;
            except IndexError:
                regular_loop=False;
        if oc_rule:
            oc_loop=True;
            white_graph=g.complement().copy();
            for e in derived_set:
                white_graph.delete_edge(e);
            for v in V:
                GNv=white_graph.subgraph(g.neighbors(v)); #The induced subgraph on N(v) of white_graph
                for C in GNv.connected_components_subgraphs():
                    deg=C.degree_sequence();
                    if min(deg)==2 and max(deg)==2 and C.order()%2==1: #That is, if C is an odd cycle
                        whole_loop=True; #something found, open whole_loop
                        for e in C.edges(labels=False):
                            derived_set.append(e);
                            white_graph.delete_edge(e);
                        for v in C.vertices():
                            queue.append(v);
                            active[v]=1;    
        else:
            whole_loop=False;
    return derived_set;

def find_Zsap(g,rule="CCRZ",oc_rule=False,get_value=False):
    """
    Input:
        g: a simple graph
        rule: rule that appplies - "CCRZ", "CCRZell", or "CCRZplus"
        oc_rule: if the odd cycle rule applies - True or False
        get_value: False, "edge", or "vertex".  
    Output:
        Return Zsap according the choice of get_value.
        Here oc_rule can be equipped or not, and the rule also varies.
        If get_value=False, then return True or False depending on Zsap=0 or not. (polynomial-time).
        If get_value="edge", then return Zsap.
        If get_value="vertex", then return Zoc.
        ** rule="CCRZplus" and get_value="vertex" is not compatable, since Zvc-oc^plus is not defined.
    """  
    mbar=g.complement().size(); #number of non-edges
    if get_value==False: #only check if [] a Zsap zero forcing set
        derived_set=Zsap_game(g,[],rule,oc_rule);
        if mbar==len(derived_set):
            return True;
        else:
            return False;
    if get_value=="edge": #number of non-edges grows up rapidly
        Ebar=g.complement().edges(labels=False);
        mbar=len(Ebar);
        lbd=-1;
        ubd=mbar;
        while ubd-lbd>=2: #apply random algorithm;
            guess=random.choice(range(lbd+1,ubd)); #take an interior point in [lbd,ubd];
            found=False;
            for B in Combinations(Ebar,guess):
                if mbar==len(Zsap_game(g,B,rule,oc_rule)):
                    found=True;
                    break;
            if found:
                ubd=guess;
            else:
                lbd=guess;
        return ubd;
    if get_value=="vertex":
        gbar=g.complement();
        Ebar=gbar.edges(labels=False);
        V=g.vertices();
        mbar=len(Ebar);
        n=g.order();
        lbd=-1;
        ubd=n;
        while ubd-lbd>=2: #apply random algorithm;
            guess=random.choice(range(lbd+1,ubd)); #take an interior point in [lbd,ubd];
            found=False;
            for sub in Combinations(V,guess):
                #build initial blue nonedges B;
                B=[];
                for ebar in Ebar:
                    i,j=ebar;
                    if i in sub or j in sub:
                        B.append(ebar);
                #build banned_dict;
                banned_dict={v:[] for v in V};
                for j in sub: ##(i:j -> k) is banned if j is in sub and {i,j} is nonedge.
                    for i in gbar.neighbors(j):
                        banned_dict[i].append(j);
                if mbar==len(Zsap_game(g,B,rule,oc_rule,banned_dict)):
                       found=True;
                       break;
            if found:
                ubd=guess;
            else:
                lbd=guess;
        return ubd; 
       	
