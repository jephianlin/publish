### load this file by load('has_SXP.sage')
### or, you may run it on SageCell server through the link
### link

### Some examples:
"""
g = graphs.PathGraph(5)
A = g.adjacency_matrix(g)
print A
print '---'

print 'SSP verification matrix:'
print verS(A)
print 'Use TSS_col_index(n) to see the column index'
print 'Here n = A.dimensions()[0]'
print 'Use ver_row_index(A) to see the row index'
print '---'


print 'has SSP?'
print has_SSP(A)
print '---'

print 'SSP tangent space matrix:'
print TSS(A)
print 'Use TSS_col_index(n) to see the column index'
print 'Use TS_row_index(n) to see the row index'
print 'Here n = A.dimensions()[0]'
"""

##### Code Starts Here ###
### set up the indices of each matrix
### use value_to_index to get the inverse map
### be aware of the inputs

def TSS_col_index(n):
    """
    Input:
        n: an integer, the order of A
    Output:
        the list [(i,j) for i<j]
        (column index of TS_S(A))
    """
    return [(i,j) for i in range(n-1) for j in range(i+1,n)]
    
def TSM_col_index(n,q):
    """
    Input:
        n: an integer, the order of A
        q: an integer, the number of distinct eigenvalues of A
           (can be computed by q = A.minpoly().degree())
    Output:
        the list [(i,j) for i<j] + [0,...,q-1]
        (column index of TS_M(A))
    """
    return TSS_col_index(n) + list(range(q))

def TSA_col_index(n):
    """
    Input:
        n: an integer, the order of A
    Output:
        the list [(i,j) for all i, j]
        (column index of TS_A(A))
    """
    return [(i,j) for i in range(n) for j in range(n)]
    
def TS_row_index(n):
    """
    Input:
        n: an integer, the order of A
    Output:
        the list [(i,j) for i<=j]
        (row index of TS_?(A))
    """
    return [(i,j) for i in range(n) for j in range(i,n)]
    
def ver_row_index(A):
    """
    Input:
        A: a real sym matrix
    Output:
        the list of zero i,j-entries 
        with 0 <= i < j <= n-1
        (row index of any verification matrix)
    """
    n = A.dimensions()[0]
    return [(i,j) for i in range(n-1) for j in range(i+1,n) if A[i,j]==0]

def value_to_index(l):
    """
    Input:
        l: a list whose values are all distinct
    Ourput:
        return a dictionary {value: index}
        for all """
    return {l[k]: k for k in range(len(l))}

def Eij(i,j,m,n=None):
    """
    Input: 
        i,j,m,n: integers
        if n is not assigned, then n=m
    Output: 
        an m x n matrix whose i,j-entry is 1 while all others are 0;
    ### starting from 0th column and 0th row;
    """
    if n == None:
        n = m;
    a = [0]*(m*n);
    a[i*n + j] = 1;
    return matrix(m,a);

def TSS(A):
    """
    Input:
        A: a real sym matrix
    Output:
        return the SSP tangent space matrix TS_S(A) of A
    """
    n = A.dimensions()[0]
    col_ind = TSS_col_index(n)
    row_ind = TS_row_index(n)
    col_inv = value_to_index(col_ind)
    row_inv = value_to_index(row_ind)
    
    mm, nn = len(row_ind), len(col_ind)
    TS = zero_matrix(A.base_ring(), mm, nn)
    for jj in range(nn):
        i,j = col_ind[jj]
        Kij = Eij(i,j,n) - Eij(j,i,n)
        tan = A*Kij + Kij.transpose()*A
        for ii in range(mm):
            u,v = row_ind[ii]
            TS[ii,jj] = tan[u,v]
    return TS

def TSM(A):
    """
    Input:
        A: a real sym matrix
    Output:
        return the SMP tangent space matrix TS_M(A) of A
    """
    q = A.minpoly().degree()
    n = A.dimensions()[0]
    row_ind = TS_row_index(n)
    row_inv = value_to_index(row_ind)
    
    mm = len(row_ind)
    extra = zero_matrix(A.base_ring(), mm, q)
    power = identity_matrix(n)
    for k in range(q):
        tan = power
        for ii in range(mm):
            u,v = row_ind[ii]
            extra[ii,k] = tan[u,v]
        power *= A
    return TSS(A).augment(extra)

def TSA(A):
    """
    Input:
        A: a real sym matrix
    Output:
        return the SAP tangent space matrix TS_A(A) of A
    """
    n = A.dimensions()[0]
    col_ind = TSA_col_index(n)
    row_ind = TS_row_index(n)
    col_inv = value_to_index(col_ind)
    row_inv = value_to_index(row_ind)
    
    mm, nn = len(row_ind), len(col_ind)
    TS = zero_matrix(A.base_ring(), mm, nn)
    for jj in range(nn):
        i,j = col_ind[jj]
        E = Eij(i,j,n)
        tan = A*E + E.transpose()*A
        for ii in range(mm):
            u,v = row_ind[ii]
            TS[ii,jj] = tan[u,v]
    return TS

def ver_rows_in_TS(A):
    """
    Input: 
        A: a real sym matrix
    Output:
        the rows in TS_?(A) 
        corresponding to the verification matrix
    """
    n = A.dimensions()[0]
    row_ind = TS_row_index(n)
    row_inv = value_to_index(row_ind)
    v_row_ind = ver_row_index(A)
    return [row_inv[ind] for ind in v_row_ind]

def verS(A):
    """
    Input:
        A: a real sym matrix
    Output:
        the SSP verification matrix of A
    """
    return TSS(A)[ver_rows_in_TS(A),:]

def verM(A):
    """
    Input:
        A: a real sym matrix
    Output:
        the SMP verification matrix of A
    """
    return TSM(A)[ver_rows_in_TS(A),:]

def verA(A):
    """
    Input:
        A: a real sym matrix
    Output:
        the SAP verification matrix of A
    """
    return TSA(A)[ver_rows_in_TS(A),:]

def has_full_row_rank(M):
    """
    Input:
        M: a matrix
    Output:
        return whether M has full row rank
    """
    m,n = M.dimensions()
    return M.rank() == m

def has_SSP(A):
    """
    Input:
        A: a real sym matrix
    Output:
        return whether A has SSP or not
    """
    return has_full_row_rank(verS(A))

def has_SMP(A):
    """
    Input:
        A: a real sym matrix
    Output:
        return whether A has SMP or not
    """
    return has_full_row_rank(verM(A))

def has_SAP(A):
    """
    Input:
        A: a real sym matrix
    Output:
        return whether A has SAP or not
    """
    return has_full_row_rank(verA(A))