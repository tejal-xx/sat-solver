from z3 import *
import sys

s = Solver()
f = open(sys.argv[1], "r")

file=[]

for line in f.read().split():
    file.append([int(x) for x in line.split(',')])

size=file[0][0]
max_moves=file[0][1]

H=[]
V=[]

mine=[]

H.append(file[1])
H[0][1]+=1

for a in file:

    if(len(a)==2):
        continue

    if(a[0]==1):
        H.append(a[1::])
        H[-1][1]+=1

    elif(a[0]==0):
        V.append(a[1::])
        V[-1][0]+=1
    else:
        mine.append(a[1::])

nh = len(H)
nv = len(V)
nm = len(mine)

mines=[]

for i in range(nm):
    mines.append(Int(f'mine_{i}'))
    s.add(mines[i]==(mine[i][0]*size+mine[i][1]))

ph = [[[0 for i in range(0,nh)] for j in range(0,max_moves+1)] for k in range(max_moves+1)]
pv = [[[0 for i in range(0,nv)] for j in range(0,max_moves+1)] for k in range(max_moves+1)]

moves=[]

for i in range(max_moves):
    moves.append(Int(f'moves_{i}'))

for i in range(nh):
    ph[0][i]=Int(f'posh_{0}_{i}')
    s.add(ph[0][i]==(H[i][0]*size+H[i][1]))

for i in range(nv):
    pv[0][i]=Int(f'posv_{0}_{i}')
    s.add(pv[0][i]==(V[i][0]*size+V[i][1]))

for i in range(1,max_moves+1):
    for j in range(nh):
        ph[i][j]=Int(f'posh_{i}_{j}')


for i in range(1,max_moves+1):
    for j in range(nv):
        pv[i][j]=Int(f'posv_{i}_{j}')

for t in range(0,max_moves):
    s.add(moves[t]<=(nh+nv)*2)
    s.add(moves[t]>=0)


for t in range(0,max_moves):
    n=0

    for c in range(0,nh):

        ap1=[]

        for d in range(0,nh):
            
            if(d==c):
                continue

            ap1.append(ph[t+1][d]==ph[t][d])

        for d in range(0,nv):
            ap1.append(pv[t+1][d]==pv[t][d])
        
        ap1.append(ph[t+1][c]==ph[t][c]+1)
        s.add(Or(Not(moves[t]==2*n),And(ap1)
))

        ap2=[]

        for d in range(0,nh):
            
            if(d==c):
                continue

            ap2.append(ph[t+1][d]==ph[t][d])

        for d in range(0,nv):
            ap2.append(pv[t+1][d]==pv[t][d])
        
        ap2.append(ph[t+1][c]==ph[t][c]-1)
        s.add(Or(Not(moves[t]==2*n+1),And(ap2)))
        n+=1

    for c in range (nv):
        ap1=[]
        for d in range(nh):
            
            ap1.append(ph[t+1][d]==ph[t][d])

        for d in range(nv):
                        
            if(d==c):
                continue

            ap1.append(pv[t+1][d]==pv[t][d])
        
        ap1.append(pv[t+1][c]==pv[t][c]+size)
        s.add(Or(And(ap1),Not(moves[t]==2*n)))

        ap2=[]

       
        for d in range(nh):

            ap2.append(ph[t+1][d]==ph[t][d])

        for d in range(nv):
            
            if(d==c):
                continue
            ap2.append(pv[t+1][d]==pv[t][d])
        
        ap2.append(pv[t+1][c]==pv[t][c]-size)

        s.add(Or(Not(moves[t]==2*n+1),And(ap2)))
        n+=1
    

    ap3=[]

    for d in range(nh):
            
        ap3.append(ph[t+1][d]==ph[t][d])

    for d in range(nv):

        ap3.append(pv[t+1][d]==pv[t][d])
    

    s.add(Or(Not(moves[t]==(2*n)),And(ap3)))


for t in range(max_moves-1):
    for c in range(nh):
        s.add(Or(ph[t+1][c]%size!=size-1, moves[t+1]!=2*c))

for t in range(max_moves):
    for c in range(nh):
        s.add(ph[t+1][c]%size!=0)

for t in range(max_moves-1):
    for c in range(0,nv):
        s.add(Or(pv[t+1][c]/size!=size-1,moves[t+1]!=2*(nh+c)))

for t in range(max_moves):
    for c in range(0,nv):
        s.add(pv[t+1][c]/size!=0)


for t in range(max_moves):
    for c in range(nh):
        for co in range(nm):
            s.add(ph[t+1][c]!=mines[co])
            s.add(ph[t+1][c]-1!=mines[co])
    for c in range(nv):
        for co in range(nm):
            s.add(pv[t+1][c]!=mines[co])
            s.add(pv[t+1][c]-size!=mines[co])


for t in range(max_moves):
    for c in range(0,nh):
        for d in range(0,nh):
            if c==d:
                continue
            s.add(Or(ph[t+1][c]%size==size-1,ph[t+1][c]+1!=ph[t+1][d]))
    for c in range(0,nv):
        for d in range(0,nv):
            if c==d:
                continue
            s.add(Or(pv[t+1][c]/size==size-1,pv[t+1][c]+size!=pv[t+1][d]))
    for c in range(0,nh):
        for d in range(0,nv):
            s.add(ph[t+1][c]!=pv[t+1][d])
            s.add(ph[t+1][c]-1!=pv[t+1][d])
            s.add(ph[t+1][c]!=pv[t+1][d]-size)
            s.add(ph[t+1][c]-1!=pv[t+1][d]-size)


s.add(ph[max_moves][0]==((H[0][0]*size)+size-1))

r = s.check()

if r==z3.sat:
    m=s.model()
    
    for i in range(0,max_moves):
        
        move = m[moves[i]].as_long()

        if move//2<nh:
            if move%2==0:
                print(m[ph[i][move//2]].as_long()//size,m[ph[i][move//2]].as_long()%size,sep=',')
            if move%2==1:
                print(m[ph[i][move//2]].as_long()//size,m[ph[i][move//2]].as_long()%size-1,sep=',')
        elif move//2<nh+nv:
            if move%2==0:
                print(m[pv[i][move//2-nh]].as_long()//size,m[pv[i][move//2-nh]].as_long()%size,sep=',')
            if move%2==1:
                print(m[pv[i][move//2-nh]].as_long()//size-1,m[pv[i][move//2-nh]].as_long()%size,sep=',')
                    
    
    
else:   
    print("unsat",flush=True)
