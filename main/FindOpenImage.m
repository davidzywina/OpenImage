/*  
    Let E/Q be a non-CM elliptic curve.   Associated to the Galois action on the torsion points of E
    is a representation rho_E: Gal_Q -> GL(2,Zhat).

    This files contains a function "FindOpenImage".   For a non-CM E/Q given by a Weierstrass equation,
    FindOpenImage(E) returns the following:
        - a group G that is the image of rho_E up to conjugacy in GL(2,Zhat); it is given by its image in GL(2,Z/NZ)
          where N is the level of G in GL(2,Zhat)
        - the index of G in GL(2,Zhat)
        - the intersection of G with SL(2,Zhat) given as a subgroup of SL(2,Z/MZ) with M>0 minimal.
        
    [ Return results are proven correct.  Trying increasing the extra parameter "Bound" in the unlikely 
    case that an error arises since the image could not be determined.   The function will always 
    return an error if E happens to come from an unknown rational point on a high genus modular curve that we missed. ]
*/


load "../precomputation/ComputeFrobData.m";  // Loads all functions we need (may take a bit!)
// In particular, this loads an array X consisting of modular curves corresponding to certain agreeable subgroups of GL(2,Zhat).
// Except for a (conjecturally) finite number of j-invariants, they encode enough info to determine the Galois images of 
// non-CM elliptic curves E/Q.

base:= [k: k in Keys(X) | X[k]`N eq 1][1]; //label of the j-line, equivalently, the group GL(2,Zhat).

// j-invariants of all CM elliptic curves over Q
CM_jInvariants:={0, 54000, -12288000, 1728, 287496, -3375, 16581375, 8000, -32768, -884736, -884736000, -147197952000, -262537412640768000};

// Sets of j-invariants of non-CM elliptic curves over Q that require special attention 
// (for example if they come from a rational points of a certain modular curve with only finite many rational points).
known_exceptional_jinvariants:=
{ -162677523113838677, -6357235796156406771/32768, -92515041526500, 
-23788477376, -1815478272, -189613868625/128, -1273201875, -297756989/2, 
-110349050625/1024, -44789760, -349938025/8, -24729001, -21024576, 
-35817550197738955933474532061609984000/2301619141096101839813550846721, 
-38575685889/16384, -425920000/243, -1723025/4, 
-227920097737283556595145924109375/602486784535040403801858901, -316368, 
-138240, -9645037507360901960000/79792266297612001, -160855552000/1594323, 
-82944, -64278657/1024, -1680914269/32768, -102400/3, -140625/8, -13824, -9317, 
-35937/4, -882216989/131072, -5000, -121945/32, 
-631595585199146625/218340105584896, -131375418677056/177978515625, 
-1159088625/2097152, -18234932071051198464000/48661191875666868481, -216, -121, 
-47675785945529664000/929293739471222707, -36, -25/2, 3375/64, 64, 
141526649406897/1973822685184, 20480/243, 351/4, 1331/8, 432, 
339071334684521624665810041360384000/480250763996501976790165756943041, 
1026895/1024, 5088980530576216000/4177248169415651, 46969655/32768, 3375/2, 
109503/64, 2048, 1906624/729, 4096, 4374, 4913, 11225615440/1594323, 
30081024/3125, 806764685224507983/56693912375296, 2268945/128, 16974593/256, 
78608, 110592, 419904, 4543847424/3125, 15084602497088704/8303765625, 
82881856/27, 777228872334890625/60523872256, 16974593, 
2672876978743335041728512000/122130132904968017083, 
215694547296795302321664/4177248169415651, 
90616364985637924505590372621162077487104/197650497353702094308570556640625, 
550731776, 68769820673/16, 210720960000000/16807, 15786448344, 38477541376, 
136878750000, 24992518538304, 6225959949099011451/32768, 
66735540581252505802048, 6838755720062350457411072 };


// Information on the (known/only?) j-invariants of non-CM E/Q arising from modular curves of prime power level 
// and genus at least 2 [from the paper of Rouse-Sutherland-(Zureick-Brown)]
exceptionaljs := [
<2, -2^18*3*5^3*13^3*41^3*107^3/17^16, 16, [[7,9,7,14], [5,6,1,11], [3,13,10,13]], "16.64.2.1">,
<2, -2^21*3^3*5^3*7*13^3*23^3*41^3*179^3*409^3/79^16, 16, [[7,9,7,14], [5,6,1,11], [3,13,10,13]], "16.64.2.1">,
<2, 257^3/2^8, 16, [[9,4,8,13], [9,1,6,5], [13,11,10,7]], "16.96.3.335">,
<2, 17^3*241^3/2^4, 16, [[3,8,4,1], [9,2,0,15], [13,5,14,1]], "16.96.3.343">,
<2, 2^4*17^3, 16, [[3,7,10,5], [13,11,10,13], [11,1,6,9]], "16.96.3.346">,
<2, 2^11, 16, [[13,7,10,1], [5,15,2,15], [9,9,14,7]], "16.96.3.338">,
<2, -3^3*5^3*47^3*1217^3/(2^8*31^8), 32, [[13,21,22,11], [1,29,22,31], [9,15,8,11], [7,18,0,19]], "32.96.3.230">,
<2, 3^3*5^6*13^3*23^3*41^3/(2^16*31^4), 32, [[13,28,6,11], [7,31,22,25], [25,9,22,23], [21,16,18,23]], "32.96.3.82">,
<5, 2^4*3^2*5^7*23^3, 25, [[19,22,4,0], [22,17,22,23]], "25.50.2.1">,
<5, 2^12*3^3*5^7*29^3/7^5, 25, [[0,18,16,10], [1,20,20,18]], "25.75.2.1">,
<7, 3^3*5*7^5/2^7, 7, [[0,1,1,0], [3,0,0,6]], "7.56.1.2">,
<11, -11*131^3, 11, [[6,5,0,4], [1,7,0,10]], "11.60.1.3">,
<11, -11^2, 11, [[6,8,0,8], [8,0,0,9]], "11.60.1.4">,
<13, 2^4*5*13^4*17^3/3^13, 13, [[1,8,8,0], [7,6,0,9]], "13.91.3.2">,
<13, -2^12*5^3*11*13^4/3^13, 13, [[1,8,8,0], [7,6,0,9]], "13.91.3.2">,
<13, 2^18*3^3*13^4*127^3*139^3*157^3*283^3*929/(5^13*61^13), 13, [[1,8,8,0], [7,6,0,9]], "13.91.3.2">,
<17, -17*373^3/2^17, 17, [[15,0,0,12], [8,13,0,12]], "17.72.1.2">,
<17, -17^2*101^3/2, 17, [[14,9,0,9], [13,14,0,13]], "17.72.1.4">,
<37, -7*11^3, 37, [[8,30,0,3], [27,18,0,18]], "37.114.4.1">,
<37, -7*137^3*2083^3, 37, [[2,35,0,11], [2,36,0,6]], "37.114.4.2">
];
elladic_exceptionaljs := { r[2] : r in exceptionaljs };
assert elladic_exceptionaljs subset known_exceptional_jinvariants;


//array for keeping track of our modular curves with prime power level and genus at most 1
agreeable_groups_prime_power_level:=AssociativeArray();
P:=[2,3,5,7,11,13];
for ell in P do
    keys_ell:=[k: k in Keys(X) | Set(PrimeDivisors(X[k]`N)) subset {ell} and X[k]`is_agreeable and X[k]`genus le 1];
    ind_ell :=[X[k]`index: k in keys_ell];
    ParallelSort(~ind_ell, ~keys_ell);
    agreeable_groups_prime_power_level[ell]:=keys_ell;
end for;
// "agreeable_groups_prime_power_level[ell]"  keeps track of modular curves with level a power of ell,
// ordered by increasing degree over the j-line.

// array for keeping track of our modular curves that arise from "unentangled" groups and having infinitely many rational points
unentangled_groups:=AssociativeArray();
keys0:=[k: k in Keys(X) | X[k]`genus le 1 and X[k]`has_infinitely_many_points and X[k]`is_entangled eq false];
for k in keys0 do
    keys:=[m: m in Keys(X) | &and[m[i] eq k[i] : i in [1..#k]]];
    ind :=[X[m]`index/X[k]`index: m in keys];
    ParallelSort(~ind, ~keys);
    unentangled_groups[k]:=keys;
end for;


// Load precomputed Frobenius data for recognizing Galois images.
I:=Open("../data-files/frob_data.dat", "r"); 
b,prime_bound:=ReadObjectCheck(I);
//prime_bound:=5;
cyclic_frobenius:=AssociativeArray();
repeat
	b,k:=ReadObjectCheck(I);
    b,a:=ReadObjectCheck(I);
    b,S:=ReadObjectCheck(I);
    if b then
        if k notin Keys(cyclic_frobenius) then
            cyclic_frobenius[k]:=AssociativeArray();
        end if;
        cyclic_frobenius[k][a]:=S;
    end if;
until not b;


// We precompute some traces of Frobenius for elliptic curves over finite fields.  Useful when working with many elliptic curves.
trace_primes:=[p: p in PrimesUpTo(256) | p ne 2];
trace_of_frobenius:=AssociativeArray();
for p in trace_primes do
    trace_of_frobenius[p]:=AssociativeArray();
    for j in GF(p) do
        if j eq 0 or j eq 1728 then
            continue j;
        end if;
        trace_of_frobenius[p][j]:=TraceOfFrobenius(EllipticCurveWithjInvariant(j));  
    end for;
end for;

// Load agreeable closure info for exceptional j-invariants
ExceptionalAgreeableClosures:=[];
I:=Open("../data-files/agreeable_closures_exceptional.dat", "r");
repeat
	b,y:=ReadObjectCheck(I);
	if b then
        ExceptionalAgreeableClosures:=ExceptionalAgreeableClosures cat [y];
	end if;
until not b;

// Load Galois image info for exceptional j-invariants
ExceptionalImages:=[];
I:=Open("../data-files/exceptional_images.dat", "r");
repeat
	b,y:=ReadObjectCheck(I);
	if b then
        ExceptionalImages:=ExceptionalImages cat [y];
	end if;
until not b;


//--------------------------------------------




function OpenImageOfTwist(E,G,d)
    /*
      Input:  
            E: a non-CM elliptic curve over Q
            G: the image of rho_E^* in GL(2,Zhat), up to conjugacy, given modulo an integer divisible by the level
            d: a nonzero rational number
      Output:
            The image of rho_{E'}^* where E' is the quadratic twist of E by d
    */

    // We may take d to be a squarefree integer
    d1:=Numerator(d);
    d1:=Sign(d1) * &*([1] cat [p: p in PrimeDivisors(d1) | IsOdd(Valuation(d1,p))]);
    d2:=Denominator(d);
    d2:=Sign(d2) * &*([1] cat [p: p in PrimeDivisors(d2) | IsOdd(Valuation(d2,p))]);

    d:=d1*d2;

    // Quadratic twist is isomorphic to E
    if d eq 1 then return G; end if;

    // Conductor of character KroneckerCharacter(d, )
    if d mod 4 eq 1 then cond:=d; else  cond:=4*d; end if;

    N:=LCM(cond,#BaseRing(G));
    G:=gl2Lift(G,N);

    gens:={};
    for g in Generators(G) do
        e:=KroneckerSymbol(d, Integers()!Determinant(g) );  
        assert e in {1,-1};
        if e eq 1 then
            gens:=gens join {g};
        else
            gens:=gens join {-g};
        end if;      
    end for;

    G_:=sub<GL(2,Integers(N))| gens>;
    return G_;
end function;

function RuleOutNormalizersOfNonsplitCartain(j : bound:=1000, Bound:=10^9)
    /* Input:  Let j be the j-invariant of a non-CM elliptic curve E over Q.

       Output: 
            S:  a finite set of primes so that the image of the Galois representation rho_{E,ell}: Gal_Q -> GL(2,Z/ell) 
                does not lie in the normalizer of a nonsplit Cartan subgroup for all ell>7 not in the set S.
        (based off the code:  https://github.com/davidzywina/SurjectivityOfGalois )

        Uses primes p up to "bound" and traces of Frobenius to directly rule out some possible images.
        Use primes p up to the larger number "Bound" to rule out possible contradictions to the uniformity conjecture
        (if the conjecture cannot be verified then the algorithm halts without output)
    */

    den:=Denominator(j);
    S:={11};	
    if den ne 1 then 
        ispow,b,e:=IsPower(den);                
        if ispow then                       	
            g:=GCD([e] cat [p^2-1: p in PrimeDivisors(b)]);
            S:=S join {ell: ell in PrimeDivisors(g)};
        end if;
    else
        Q:=PrimeDivisors(Numerator(j-1728));
        Q:=[q: q in Q | q ne 2 and IsOdd(Valuation(j-1728,q))];
        if Valuation(j,2) in {3,6,9} then Q:=[2] cat Q; end if;

        p:=3;
        alpha:=[]; 
        beta:=[];
        repeat  
            a:=0;   
            while a eq 0 do
                repeat  
                    p:=NextPrime(p);                 
                until den mod p ne 0 and GF(p)!j notin {GF(p)!0,GF(p)!1728};
                j0:=GF(p)!j;
                if p in Keys(trace_of_frobenius) then
                    a:=trace_of_frobenius[p][j0];    // If already computed trace of Frobenius (up to sign)
                else
                    E:=EllipticCurve([ -27*j0*(j0-1728), 54*j0*(j0-1728)^2 ]);     // has j-invariant j0   
                    a:=TraceOfFrobenius(E);
                end if;
            end while;                   
            S:=S join {ell : ell in PrimeDivisors(a)};

            alpha:= alpha cat [[(1-KroneckerSymbol(q,p)) div 2 : q in Q]];   
            beta:= beta cat [ [(1-KroneckerSymbol(-1,p)) div 2] ];
            A:=Matrix(GF(2),alpha);  
            b:=Matrix(GF(2),beta);              
        until IsConsistent(Transpose(A),Transpose(b)) eq false; 	
    end if;	

    S:={11} join {ell: ell in S | ell gt 19 };   
    // Recent work on Chabauty rules out 13 and 17 (see https://arxiv.org/abs/2101.01862v2 )

    // use traces of Frobenius with the finitely many primes ell in S
    p:=3;
    repeat
        repeat  
            p:=NextPrime(p);                 
        until den mod p ne 0 and GF(p)!j notin {GF(p)!0,GF(p)!1728};
        j0:=GF(p)!j;

        if p in Keys(trace_of_frobenius) then
            a:=trace_of_frobenius[p][j0];
        else            
            E:=EllipticCurve([ -27*j0*(j0-1728), 54*j0*(j0-1728)^2 ]);       
            a:=TraceOfFrobenius(E);
        end if;

        for ell in S do
            if ell ne p and a mod ell ne 0 and KroneckerSymbol(a^2-4*p,ell) eq 1 then
                S:=S diff {ell};
            end if;
        end for;                  
    until S eq {} or (S eq {11} and p gt bound) or (p gt Bound);

    if S subset {11} eq false then
        "Need to consider more primes or a conjecture to Serre's uniformity questions found."; S;
        assert false;
    end if;
    return S;
end function;

function LiftQpoints(phi,S)
    /*
        Input:  
            phi: a nonconstant morphism C'->C between curves over Q
            S  : a set of rational points on C
        Output:
            The set of rational points P in C'(Q) which phi(P) in S.


        Remark:  Equivalently, we are looking for rational points on the Q-schemes Z:=phi^(-1)(P) with P in S.
            For most cases, we use "Points(Z)" to find these points.  The exception is in the important special cases
            where C' is P^1 or an elliptic curve; in these cases we reduce finding rational points to finding the 
            roots of a single polynomial in Q[x] (this turns out to be significantly faster when implemented).
    */

    C0:=Codomain(phi);
    C1:=Domain(phi);   
    // phi: C1 -> C0

    Pol<t>:=PolynomialRing(Rationals());

    S:={C0!P:P in S}; 
    S1:={};
    for P in S do

        Z:=Pullback(phi,P);
        assert Type(Z) in {MakeType("Pt"), MakeType("Sch")};
        if Type(Z) eq MakeType("Pt") then         
            S1:=S1 join {Z};
        else
            pol:=DefiningPolynomials(Z);

            if Genus(C1) eq 0 and DefiningPolynomials(C1) eq [] and #pol eq 1 then
                // In the case where C1 is the projective line, we can find the rational points on Z
                // by finding the roots of a polynomial (this is faster than using Points(Z))
                f:=pol[1];                
                S0:={ C1![r[1],1] : r in Roots( Evaluate(f,[t,1]) ) };
                if Evaluate(f,[1,0]) eq 0 then
                    S0:=S0 join { C1![1,0] };
                end if;
              
            elif Genus(C1) eq 1 and Type(C1) eq MakeType("CrvEll") then
                //In this case, C1 is an elliptic curve given by a Weierstrass equation.
                F<x>:=FunctionField(Rationals());
                PolY<y>:=PolynomialRing(F);
                RR:=quo<PolY | [ PolY!Evaluate(g,[x,y,1]): g in DefiningPolynomials(C1)]>;

                gg:=[];
                for f0 in pol do
                    f:=Evaluate(f0,[x,y,1]);             
                    a:=aInvariants(C1);
                    fc:=Evaluate(f,-y-a[1]*x-a[3]);   // using negation on E
                    g:=F!(RR!(f*fc));   // Polynomial in Q[x]                    
                    assert Denominator(g) eq 1;
                    gg:=gg cat [Numerator(g)];
                end for;

                // Now find a finite set of points that contains Z(Q).
                R0:={r[1] : r in Roots(GCD(gg))};
                f:=DefiningPolynomial(C1);
                S0:={C1![0,1,0]};
                for r in R0 do
                    S0:=S0 join {C1![r,y[1],1]: y in Roots(Evaluate(f,[r,t,1]))};
                end for;
                // Check which are actually in Z(Q)
                S0:={P: P in S0 | &and[Evaluate(f,Eltseq(P)) eq 0: f in pol]};
            else
                S0:=Points(Z);
            end if;

            S1:= S1 join S0;        
        end if;
    end for;

    S1:={C1!P: P in S1};
    S1:={P: P in S1 | phi(P) in S};

    return S1;
end function;



function FindAgreeableClosure(j :bound:=80, Bound:=10^7, minimal:=true, assume_uniformity_conjecture:=false, use_exceptional_data:=true)
    /*
        Input: 
            j: the j-invariant of a non-CM elliptic curve E/Q.

        The group GE:=rho_E^*(Gal_Q) lies in a minimal agreeable subgroup G of GL(2,Zhat), i.e., G is the agreeable closure of GE.

        Output:  a boolean "b" and a sequence "label".

            If the boolean b is true, then X_G(Q) will be infinite.

            Suppose b is true:  By construction, G up to conjugacy will be described by a unique element of our array X of modular curves.
            The sequence "label" is the key for this entry.    In this cases, we also return a set S consisting of the rational points 
            of X[label] that lie over the j-invariant j.

            Suppose b is false:  Then "label" is a sequence describing a group G0 that contains G, up to conjugacy, for which X_G0 has only finite 
            many rational points (the group G0 is our best guess for G using the modular curves we have computed).   In this case, we also return
            the group G.
            [When "use_exceptional_data" is set to false, we return G0 instead and there may be a finite number of cases where b is wrongly
             false. The main use of this is for our computation of exceptional G that we did in the precomputation.]  


        If the parameter "minimal" is false and b is true, we instead return the label for a larger agreeable group G that has 
        the same commutator subgroup.

        The quantity "bound" bounds the primes we use traces of Frobenius with before using the equations for curves directly.
        The quantity "Bound" bounds the primes we use to rule out rational points over j on some of the higher genus modular curves of
        prime power level from the paper of Rouse-Sutherland-(Zurieck-Brown).   The function will halt if it can not rule out such points.

        If "assume_uniformity_conjecture" is set to true, we assume that the subgroup rho_{E,ell}(Gal_Q) of GL(2,Z/ell) is not contained 
        in the normalizer of a nonsplit Cartan for all primes ell>13.   This can significantly speed up the computation since it will no
        longer requires factoring integers.
    */

    if use_exceptional_data and (j in known_exceptional_jinvariants and j in {t[1]: t in ExceptionalAgreeableClosures}) then
        assert exists(t){t: t in ExceptionalAgreeableClosures | t[1] eq j};
        return t[2], t[3], t[4];
    end if;

    assert j notin CM_jInvariants;  // j should be the j-invariant of a non-CM curve
    
    if assume_uniformity_conjecture eq false then
        S:=RuleOutNormalizersOfNonsplitCartain(j:bound:=Maximum(bound,1000), Bound:=Maximum(Bound,10^7));
    else
        S:={11};
    end if;
    assert S subset {11};  //otherwise, we found a counterexample to Serre's uniformity question (or more likely need more primes)

    // Prepare some relevant traces of frobenius
    den:=Denominator(j);
    PP:=[p: p in trace_primes | p le bound and p ge 3 and den mod p ne 0 and GF(p)!j notin {GF(p)!0,GF(p)!1728} ];
    trace_of_frobenius_E:=[<p,trace_of_frobenius[p][GF(p)!j]> : p in PP ];

    // Directly check if we can rule out the image mod 11 lying in the normalizer of a nonsplit Cartan
    if 11 in S then
        for b in trace_of_frobenius_E do
            p:=b[1]; if p eq 11 then continue b; end if;
            a:=b[2];                
            if a mod 11 ne 0 and KroneckerSymbol(a^2-4*p,11) eq 1 then
                S:=S diff {11};
                break b;
            end if;
        end for;
    end if;

    S:=S join {2,3,5,7}; 

    _:=exists(base){k: k in Keys(X) | X[k]`degree eq 1}; // find label "base" for j-line

    // array for keeping track of rational points above j on our modular curves
    Qpoints_above_j:=AssociativeArray();
    Qpoints_above_j[base]:={X[base]`C![j,1]};  // the point [j,1] on the j-line

    // We first consider prime power levels and modular curves of genus of at most 1
    for ell in [2,3,5,7,11,13] do 
        keys_ell:=agreeable_groups_prime_power_level[ell];

        for i in [1..#keys_ell] do
            k:=keys_ell[i];
            if X[k]`degree eq 1 then continue i; end if; // ignore j-line
            b:=X[k]`pi[1]; // have map of modular curves X[k]->X[b]
            
            if #Qpoints_above_j[b] eq 0 then  
                // No rational points to lift from lower curve
                Qpoints_above_j[k]:={};
                continue i;
            end if;

            if ell eq 11 and X[k]`degree eq 55 and ell notin S then  
                // Case with image mod 11 inside the normalizer of a non-split Cartan
                // If ell=11 is not in S, then we can already rule it out.
                Qpoints_above_j[k]:={};
                continue i;
            end if;

            // In some cases, the traces of frobenius will quickly rule out rational points
            N:=X[k]`N;
            
            for b in trace_of_frobenius_E do
                p:=b[1]; if p eq ell or N mod p eq 0 then continue b; end if;
                a:=b[2];                
                if [Integers(N)!a,Integers(N)!p] notin X[k]`trdet then
                    Qpoints_above_j[k]:={};
                    continue i;
                end if;
            end for;

            // We now lift rational points directly 

            if X[k]`genus eq 1 and X[k]`N eq 11 and X[k]`has_infinitely_many_points then
                // This is the special case of X_{ns}^+(11).  It is an elliptic curve over Q
                // whose Mordell-Weil group is free of rank 1.   It is a degree 55 cover of the j-line,
                // so it is better to treat directly rather than set up a horrible system of equations. 
                A,f:=MordellWeilGroup(X[k]`C);
                P0:=f(A.1);
                ht_j:=Height(j);
                pts:={};
                e:=0;
                repeat
                    Q1:=(X[k]`map_to_jline[1])( e*P0 );
                    Q2:=(X[k]`map_to_jline[1])(-e*P0 );
                    if j eq Q1[1]/Q1[2] then                        
                        pts:=pts join {e*P0};
                    elif j eq Q2[1]/Q2[2] then
                        pts:=pts join {-e*P0};
                    end if;		
                    e:=e+1;
                until e ge 7 and HeightOnAmbient(Q1) gt ht_j and HeightOnAmbient(Q2) gt ht_j;
                // for e>5, ht(J(e*P0)) and ht(J(-e*P0)) are strictly increasing, where
                // J is the map from our model to the j-line and ht is the naive height.
                
                Qpoints_above_j[k]:=pts;

            elif X[k]`genus le 1 then
                // Main case!
                phi:=map<X[k]`C->X[b]`C | X[k]`pi[2]>;
                pts:=Qpoints_above_j[b];
                Qpoints_above_j[k]:=LiftQpoints(phi,pts);
            end if;

        end for;
    end for;


    // We now compute the label "label" of a minimal unentangled agreeable subgroup of GL(2,Zhat) whose ell-adic projections
    // give modular curves of genus at most 1 and contains G_E where E/Q has j-invariant j.
    P:=[ 2, 3, 5, 7, 11, 13 ];
    label:=base;
    for i in [1..#P] do
        ell:=P[i];    
        m:=[k: k in agreeable_groups_prime_power_level[ell] | Qpoints_above_j[k] ne {}];
        label[i]:=m[#m][i];   // recall we ordered keys by increasing degree over j-line
    end for;

    // The above label does not take into account cases when the ell-adic images give rise to genus >1 modular curves
    // arising from an agreeable group; we now work that out.

    if j in elladic_exceptionaljs then  
        //cases where we know that their are relevant exceptional ell-adic images 

        Gs:=[]; // sequence for keeping track of ell-adic images
        P:=[2,3,5,7,11,13,17,19,37];

        for i in [1..#P] do
            for r in exceptionaljs do
                if r[2] eq j and r[1] eq P[i] then
                    label[i]:=r[5];  // adjust label
                    Gs:=[ sub<GL(2,Integers(r[3]))| r[4]> ];
                    ell:=r[1];
                    break i; // can check that there is at most one exceptional prime for each j
                end if;
            end for;
        end for;

        for i in [1..#P] do
            if P[i] eq ell then continue i; end if;
            if label[i] ne "1A0-1a" then
                k:=[k:k in Keys(X) | X[k]`degree eq 1][1]; // j-line label
                k[i]:=label[i];
                assert k in Keys(X);
                Gs:=Gs cat [X[k]`G];
            end if;
        end for;

        N:=&*[#BaseRing(G): G in Gs];
        Gs:=[gl2Lift(G,N): G in Gs];
        G:=&meet Gs;    
        
        // We want our group to contain the scalar matrices (since agreeable groups have this property)
        GL2:=GL(2,BaseRing(G));
        G:=sub<GL2| Generators(G) join Generators(Center(GL2))>;

        //"Exceptional point on modular curve of prime power order.";
        return false, label, G;
        
    end if;


    // There are a few modular curves of genus >1 and prime power level in Rouse-Sutherland-(Zureick-Brown) whose
    // rational points were not completely determined.    We can rule out these images by traces of Frobenius data.
    //  The following checks if this needs to be done and if so, does it.

    level:=[]; gens:=[]; trdet:=[];        // 1/6, 3/14, 1/5, 9/28. 2/7, 5/22

    // "27.243.12.1"   "9G0-9a"   (first label is from RSZB and covers the 2nd label's curve)
    if #Qpoints_above_j[["1A0-1a","9G0-9a","1A0-1a","1A0-1a","1A0-1a","1A0-1a","1A0-1a","1A0-1a","1A0-1a"]] ne 0 then
        level:=level cat [27];    // level of group
        gens:=gens cat [  [[ 7, 5, 11, 20 ],[ 8, 20, 10, 8 ]] ];  // generators of group
        trdet:=trdet cat [{[18, 11], [9, 2], [18, 8], [9, 5], [18, 23], [18, 20], [9, 8], [9, 11], [18, 17], [9, 17], [9, 14], [18, 26], [9, 20], 
            [18, 5], [9, 23], [18, 2], [9, 26], [18, 14]}];  // pairs of traces and determinants for elements in group
    end if;

    // "25.250.14.1"  "5C0-5a"
    if #Qpoints_above_j[["1A0-1a","1A0-1a","5C0-5a","1A0-1a","1A0-1a","1A0-1a","1A0-1a","1A0-1a","1A0-1a"]] ne 0 then
        level:=level cat [25]; 
        gens:=gens cat [[[ 16, 21, 8, 9 ],[ 11, 7, 14, 11 ]]];
        trdet:=trdet cat [{ [10,21], [10,19], [20,16], [20,19], [10,16], [15,14], [20,24], [15,11], [15,9], [15,6], [15,4], [15,1], [15,24], [5,4], 
            [15,21], [5,6], [15,19], [5,1], [15,16], [10,14], [5,14], [10,11], [5,9], [10,9], [5,11], [5,21], [10,6], [20,4], [20,6], 
            [10,4], [20,1], [5,16], [10,1], [5,19], [20,14], [20,9], [5,24], [20,11], [10,24], [20,21] }];
    end if;
    
    // "49.1029.69.1"       "7D0-7a"
    if #Qpoints_above_j[["1A0-1a","1A0-1a","1A0-1a","7D0-7a","1A0-1a","1A0-1a","1A0-1a","1A0-1a","1A0-1a"]] ne 0 then
        level:=level cat [49]; 
        gens:=gens cat [[[ 6, 32, 39, 43 ],[ 30, 4, 8, 19 ]]];
        trdet:=trdet cat [{ [7,6], [21,47], [7,5], [21,41], [7,3], [21,40], [7,13], [7,12], [14,3], [7,10], [14,6], [14,5], [7,20], [7,19], [28,48], 
            [14,10], [7,17], [28,45], [7,31], [14,13], [28,47], [14,12], [14,19], [28,41], [7,27], [28,40], [7,26], [14,17], [7,24], 
            [7,38], [14,20], [28,38], [14,27], [28,33], [14,26], [7,34], [7,33], [28,34], [14,24], [14,31], [7,47], [28,31], [7,45], 
            [14,34], [28,24], [28,27], [14,33], [28,26], [7,41], [7,40], [28,20], [14,38], [28,17], [28,19], [14,41], [14,40], [28,13], 
            [14,47], [7,48], [28,12], [14,45], [28,10], [14,48], [28,5], [28,6], [35,48], [28,3], [35,41], [35,40], [35,47], [35,45], 
            [35,34], [35,33], [35,38], [35,27], [35,26], [35,24], [35,31], [42,13], [42,12], [42,10], [35,19], [35,17], [42,6], [42,5], 
            [42,3], [35,20], [35,10], [42,31], [35,13], [42,27], [35,12], [42,26], [35,3], [42,24], [35,6], [42,20], [35,5], [42,19], 
            [42,17], [42,47], [42,45], [42,41], [42,40], [42,38], [42,34], [42,33], [42,48], [21,20], [21,17], [21,19], [21,31], [21,24], 
            [21,27], [21,26], [21,5], [21,6], [21,3], [21,13], [21,12], [21,10], [21,48], [21,38], [21,33], [21,34], [21,45] }];
    end if;
    
    // "49.147.9.1"     "7D0-7a"
    if #Qpoints_above_j[["1A0-1a","1A0-1a","1A0-1a","7D0-7a","1A0-1a","1A0-1a","1A0-1a","1A0-1a","1A0-1a"]] ne 0 then
        level:=level cat [49]; 
        gens:=gens cat [[[ 0, 48, 43, 14 ],[ 28, 38, 45, 9 ]]];
        trdet:=trdet cat [{ [3,27], [3,26], [3,19], [3,22], [3,20], [3,8], [3,15], [3,12], [3,1], [3,6], [39,36], [39,34], [39,33], [39,47], [39,43], 
            [3,48], [39,40], [3,43], [34,20], [3,41], [34,18], [3,40], [34,17], [3,47], [39,48], [3,34], [3,33], [34,25], [34,24], [34,6], 
            [3,36], [39,6], [39,5], [34,4], [34,3], [27,48], [39,15], [34,13], [39,13], [34,11], [34,10], [39,8], [39,22], [39,20], [39,19], 
            [27,34], [27,32], [34,48], [27,39], [27,38], [39,29], [32,48], [39,27], [39,26], [27,41], [34,38], [27,45], [27,18], [34,34], 
            [27,17], [34,32], [34,46], [34,45], [27,20], [32,33], [27,27], [27,25], [32,34], [34,41], [9,33], [27,31], [32,36], [9,37], 
            [32,41], [27,3], [32,40], [32,43], [9,38], [9,40], [27,6], [32,47], [27,4], [27,11], [9,44], [27,10], [9,47], [9,17], [9,23], 
            [32,27], [32,26], [32,29], [9,24], [9,26], [32,1], [9,31], [9,30], [32,5], [9,3], [9,2], [32,6], [9,5], [32,8], [9,9], [32,13], 
            [32,12], [32,15], [9,10], [9,12], [36,20], [36,17], [36,18], [36,31], [36,25], [36,24], [36,27], [36,4], [36,6], [36,3], [36,13], 
            [36,48], [36,39], [36,38], [36,32], [36,45], [36,46], [36,41], [6,11], [6,10], [6,13], [6,6], [6,4], [6,27], [6,25], [6,24], [6,31], 
            [6,17], [6,41], [6,46], [6,45], [12,9], [6,34], [6,32], [12,10], [6,39], [12,5], [6,38], [12,3], [12,2], [12,30], [12,24], [6,48], 
            [12,26], [12,17], [12,16], [12,19], [12,45], [12,44], [12,47], [12,40], [12,37], [12,38], [12,33], [26,31], [26,30], [26,26], [26,24], 
            [26,23], [46,34], [46,33], [26,19], [26,17], [26,16], [46,36], [46,43], [46,41], [26,12], [46,40], [46,47], [26,10], [26,9], [26,5], 
            [46,48], [26,3], [26,2], [22,48], [22,41], [22,45], [46,1], [22,34], [46,6], [22,32], [22,39], [26,47], [22,38], [26,45], [22,27], 
            [46,8], [46,15], [22,25], [22,31], [46,12], [46,19], [26,37], [22,18], [22,17], [26,33], [46,22], [46,20], [46,27], [46,26], [22,20], 
            [22,11], [22,10], [22,3], [22,6], [22,4], [43,6], [43,4], [43,11], [43,10], [43,13], [43,17], [43,27], [43,25], [43,24], [43,31], 
            [43,34], [43,32], [43,39], [43,38], [43,41], [43,46], [43,45], [2,38], [2,37], [43,48], [2,47], [38,43], [2,45], [38,41], [2,44], 
            [38,47], [2,40], [2,23], [38,34], [38,33], [2,19], [2,17], [2,16], [2,31], [2,30], [2,26], [2,5], [38,48], [2,3], [2,12], [38,8], 
            [38,15], [2,10], [2,9], [38,13], [38,12], [38,1], [38,5], [38,27], [38,26], [38,29], [38,19], [38,22], [38,20], [10,47], [10,43], 
            [10,40], [10,36], [10,34], [10,33], [10,48], [10,15], [10,13], [5,5], [10,8], [10,6], [10,5], [5,2], [5,12], [5,9], [10,29], 
            [5,10], [10,27], [10,26], [5,23], [5,17], [5,16], [10,22], [5,19], [10,20], [10,19], [5,31], [5,30], [5,24], [5,26], [5,38], [5,33], 
            [5,45], [5,44], [5,40], [48,32], [48,34], [48,39], [48,38], [48,41], [48,46], [48,48], [48,3], [48,4], [25,1], [48,11], [25,5], 
            [48,10], [48,13], [25,6], [25,8], [48,17], [25,13], [48,18], [25,12], [25,15], [48,20], [25,19], [48,24], [48,27], [25,20], [25,22], 
            [48,31], [25,27], [25,29], [25,33], [23,23], [25,34], [25,36], [23,19], [23,17], [25,41], [23,16], [25,40], [23,31], [23,30], [25,47], 
            [23,26], [23,24], [33,40], [23,5], [23,3], [33,45], [23,2], [33,44], [33,47], [33,33], [23,12], [33,37], [23,10], [23,9], [33,38], 
            [33,9], [23,37], [33,10], [33,12], [23,33], [23,47], [23,45], [33,3], [33,2], [33,24], [33,26], [33,31], [33,16], [33,19], [33,23], 
            [44,45], [44,44], [44,40], [44,38], [44,33], [44,12], [44,9], [44,10], [44,5], [44,2], [44,31], [44,30], [44,24], [44,26], [44,23], 
            [44,17], [44,16], [44,19], [13,45], [13,46], [13,41], [15,13], [13,39], [15,11], [13,38], [15,10], [13,32], [15,6], [15,4], [15,3], 
            [15,25], [13,48], [15,24], [13,13], [47,47], [15,20], [47,45], [47,44], [15,18], [15,17], [47,40], [15,46], [15,45], [47,38], [13,4], 
            [47,37], [13,6], [15,41], [13,3], [15,38], [13,31], [15,34], [13,25], [31,29], [13,24], [15,32], [13,27], [31,26], [13,20], [16,3], 
            [13,17], [31,22], [16,2], [31,20], [31,19], [13,18], [16,9], [17,27], [47,12], [17,26], [16,10], [31,13], [47,10], [17,29], [15,48], 
            [31,12], [47,9], [16,12], [47,5], [31,8], [16,16], [16,19], [40,9], [31,6], [47,3], [31,5], [40,10], [16,23], [47,31], [47,30], [40,12], 
            [31,1], [17,8], [16,24], [16,26], [47,26], [17,13], [17,12], [40,3], [17,15], [40,2], [16,31], [40,5], [47,23], [17,1], [16,33], [4,48], 
            [47,19], [17,5], [40,24], [16,37], [47,17], [47,16], [40,26], [17,6], [16,38], [31,48], [40,31], [16,40], [40,30], [31,47], [40,17], 
            [16,45], [4,36], [16,44], [31,43], [16,47], [4,33], [31,41], [17,48], [40,23], [31,40], [40,40], [31,36], [31,34], [4,41], [40,44], 
            [17,41], [4,40], [40,47], [17,40], [4,43], [17,43], [40,33], [4,20], [17,47], [4,22], [40,37], [17,33], [4,19], [40,38], [17,34], [4,29], 
            [17,36], [30,33], [30,38], [30,37], [4,27], [4,26], [4,5], [30,40], [4,6], [30,47], [4,1], [30,45], [18,36], [30,44], [30,19], [4,13], 
            [18,34], [4,12], [30,17], [4,15], [30,16], [18,47], [30,23], [18,43], [18,41], [18,40], [30,24], [30,31], [30,30], [30,3], [30,2], 
            [37,37], [18,48], [37,38], [30,5], [37,33], [37,45], [37,44], [37,47], [18,6], [18,5], [30,12], [37,40], [18,1], [18,13], [18,12], 
            [18,8], [18,22], [18,20], [18,19], [24,27], [24,29], [37,5], [18,29], [24,19], [18,26], [37,3], [37,2], [24,20], [24,22], [37,9], 
            [24,8], [37,10], [24,13], [24,12], [1,11], [24,15], [1,10], [1,13], [24,1], [37,17], [37,16], [37,19], [24,5], [1,3], [24,6], [37,30], 
            [1,4], [37,24], [37,26], [1,24], [1,27], [1,31], [1,17], [1,18], [24,41], [1,20], [24,40], [1,41], [8,45], [24,47], [8,46], [24,33], 
            [1,46], [29,45], [24,34], [8,34], [1,32], [24,36], [29,46], [1,34], [8,39], [29,41], [11,34], [11,33], [1,39], [1,38], [29,39], [29,38], 
            [11,43], [29,32], [11,41], [29,34], [8,48], [11,47], [1,48], [29,31], [29,25], [29,24], [29,27], [11,48], [8,11], [8,10], [29,20], [8,13], 
            [19,40], [19,47], [29,18], [8,3], [29,13], [19,45], [19,44], [8,4], [19,33], [8,6], [8,25], [29,11], [11,1], [8,24], [29,10], [19,38], 
            [8,27], [19,37], [11,5], [29,6], [8,31], [8,17], [29,3], [11,8], [11,15], [8,18], [11,13], [8,20], [11,12], [11,19], [11,22], [11,20], 
            [11,27], [11,26], [19,12], [19,3], [11,29], [19,2], [19,5], [19,24], [19,31], [19,30], [19,19], [19,17], [19,16], [19,23], [41,17], 
            [41,18], [41,20], [41,25], [41,24], [41,27], [41,31], [41,3], [41,4], [41,6], [41,11], [41,10], [41,13], [41,48], [41,34], [41,39], 
            [41,45], [41,46], [45,13], [45,12], [45,15], [45,5], [45,6], [45,1], [20,39], [20,38], [20,32], [45,29], [20,34], [20,45], [20,46], 
            [45,27], [20,41], [45,26], [45,20], [45,22], [45,19], [45,41], [45,40], [45,43], [45,36], [45,33], [20,6], [20,3], [20,13], [20,11], 
            [20,10], [20,20], [45,48], [20,18], [20,31], [20,25], [20,24], [20,27] }];
    end if;
    
    // "49.196.9.1"     "7F0-7a"
    if #Qpoints_above_j[["1A0-1a","1A0-1a","1A0-1a","7F0-7a","1A0-1a","1A0-1a","1A0-1a","1A0-1a","1A0-1a"]] ne 0 then
        level:=level cat [49]; 
        gens:=gens cat [[[ 18, 29, 45, 38 ],[ 11, 0, 35, 3 ]]];
        trdet:=trdet cat [{ [38,9], [17,10], [38,3], [38,2], [17,3], [17,2], [48,5], [38,31], [38,30], [48,8], [38,17], [48,12], [38,16], [48,15], [48,19], [48,22], 
            [17,45], [48,26], [48,29], [17,37], [17,38], [30,48], [30,34], [30,32], [30,39], [30,41], [30,46], [30,20], [30,27], [30,25], [30,4], 
            [30,11], [30,13], [8,40], [8,43], [23,20], [23,18], [8,47], [8,33], [23,27], [8,36], [23,25], [23,6], [22,40], [23,4], [22,33], [45,9], 
            [23,11], [45,10], [22,36], [22,26], [8,8], [45,3], [45,2], [22,29], [8,12], [22,19], [23,48], [45,31], [45,30], [8,1], [45,24], [22,22], 
            [45,23], [45,17], [22,8], [22,15], [26,27], [8,26], [8,29], [26,25], [23,34], [45,45], [22,12], [45,44], [23,32], [22,1], [23,46], [26,20], 
            [8,19], [26,18], [22,5], [45,37], [23,41], [8,22], [9,48], [26,11], [26,6], [26,4], [9,34], [9,39], [9,41], [26,48], [26,46], [9,46], [26,41], 
            [9,18], [9,20], [9,25], [39,38], [26,34], [39,37], [26,32], [39,45], [39,44], [9,4], [9,6], [9,11], [9,13], [39,3], [39,10], [39,9], [39,23], 
            [39,16], [39,31], [39,30], [39,24], [10,45], [10,44], [10,38], [6,8], [10,37], [6,15], [6,1], [6,5], [6,26], [6,29], [6,19], [6,22], [10,10], 
            [10,9], [6,43], [6,40], [6,47], [10,3], [10,31], [6,33], [10,30], [10,24], [10,23], [16,4], [20,36], [16,6], [20,33], [10,16], [16,13], 
            [20,47], [20,40], [16,18], [20,43], [16,25], [16,27], [44,46], [16,32], [16,34], [20,5], [16,39], [44,39], [16,41], [20,1], [44,32], [44,34], 
            [20,12], [16,46], [20,15], [16,48], [20,22], [44,48], [44,13], [20,29], [44,11], [20,26], [44,4], [44,6], [1,8], [44,27], [3,24], [44,20], 
            [3,31], [1,12], [1,15], [3,30], [41,19], [44,18], [3,17], [1,5], [3,16], [41,22], [3,23], [41,26], [41,29], [3,10], [1,26], [1,29], [41,1], 
            [1,19], [3,2], [41,8], [1,22], [1,40], [1,43], [41,12], [1,47], [1,36], [41,33], [3,45], [3,44], [41,36], [41,40], [3,38], [41,43], [3,37], 
            [11,38], [11,37], [41,47], [11,45], [11,44], [11,3], [11,2], [11,10], [24,24], [11,9], [24,31], [24,30], [24,17], [24,16], [11,17], [11,16], 
            [24,23], [24,9], [19,41], [24,10], [11,31], [11,30], [19,46], [19,34], [29,47], [24,3], [19,32], [24,2], [19,39], [29,40], [29,43], [29,36], 
            [29,33], [29,29], [19,48], [29,26], [19,11], [29,22], [24,44], [19,13], [29,12], [29,15], [19,4], [24,38], [19,27], [29,5], [19,25], [29,1], 
            [19,20], [27,33], [15,15], [27,36], [15,12], [27,40], [15,8], [27,19], [15,5], [15,1], [27,22], [27,26], [27,29], [33,41], [15,22], [34,22], 
            [27,1], [15,19], [34,19], [33,46], [27,5], [15,47], [33,32], [33,34], [15,43], [27,8], [27,15], [33,39], [15,40], [27,12], [15,36], [34,5], 
            [15,33], [34,1], [33,48], [34,15], [34,12], [34,8], [33,13], [5,4], [33,4], [5,6], [33,6], [33,25], [33,27], [5,13], [34,36], [34,33], [5,11], 
            [34,47], [33,18], [5,20], [34,43], [34,40], [5,18], [5,27], [5,39], [5,32], [5,34], [32,37], [32,38], [5,46], [31,31], [32,45], [32,17], [32,16], 
            [31,24], [5,48], [31,23], [32,23], [31,17], [12,13], [32,24], [31,16], [12,11], [32,30], [31,9], [12,4], [32,3], [12,6], [32,2], [31,3], [43,1], 
            [31,2], [32,9], [43,5], [32,10], [12,25], [12,27], [43,8], [12,20], [43,15], [43,19], [12,18], [43,22], [12,41], [31,45], [31,44], [43,26], 
            [36,19], [36,29], [12,39], [43,29], [31,38], [31,37], [12,32], [12,34], [36,26], [43,33], [36,5], [36,1], [43,43], [18,38], [43,40], [18,37], 
            [43,47], [36,12], [36,15], [36,8], [18,45], [18,44], [36,36], [36,33], [47,46], [36,47], [18,3], [18,2], [47,41], [36,43], [47,39], [18,9], 
            [47,32], [18,23], [18,17], [18,16], [18,31], [47,48], [18,24], [47,13], [47,11], [47,6], [47,27], [47,25], [47,20], [47,18], [37,39], [37,32], 
            [37,34], [25,3], [25,2], [37,41], [25,9], [25,10], [25,17], [25,16], [25,23], [25,24], [37,4], [37,6], [25,31], [40,11], [25,30], [37,13], 
            [40,13], [2,48], [37,11], [25,38], [37,20], [40,4], [2,39], [40,6], [40,25], [25,44], [37,18], [2,32], [2,46], [37,25], [37,27], [40,18], [2,41], 
            [40,20], [40,41], [2,20], [2,18], [40,46], [2,27], [40,34], [2,25], [40,39], [2,6], [2,13], [40,48], [2,11], [13,47], [13,43], [13,36], [13,33], 
            [46,38], [46,37], [46,45], [13,12], [46,44], [13,15], [13,8], [13,5], [13,1], [13,29], [46,2], [13,26], [46,10], [13,19], [46,17], [46,16], [46,23], 
            [46,24], [46,31], [46,30], [4,37], [4,45], [4,44], [4,23], [4,17], [38,45], [38,44], [4,31], [4,30], [38,38], [38,37], [4,24], [48,36], [17,24], 
            [48,40], [48,43], [4,3], [17,30], [4,2], [17,17], [17,16], [48,47], [4,9], [17,23], [4,10], [17,9], [38,10] }];
        end if;

    // "121.6655.511.1"     "11C1-11a"
    if #Qpoints_above_j[["1A0-1a","1A0-1a","1A0-1a","1A0-1a","11C1-11a","1A0-1a","1A0-1a","1A0-1a","1A0-1a"]] ne 0 then
        level:=level cat [121]; 
        gens:=gens cat [[[ 61, 83, 83, 60 ],[ 98, 111, 118, 23 ]]];
        trdet:=trdet cat [{ [22,57], [22,63], [22,62], [22,61], [22,51], [22,50], [22,54], [22,52], [22,43], [22,41], [22,40], [22,46], [22,35], [22,32], [22,39], [22,24], 
            [22,30], [22,29], [22,28], [22,19], [22,18], [22,17], [22,21], [22,10], [22,8], [22,13], [22,2], [22,7], [22,6], [22,120], [22,112], [22,118], 
            [22,117], [22,116], [22,107], [22,106], [22,105], [22,109], [22,98], [22,96], [22,101], [22,90], [22,95], [22,94], [22,83], [22,87], [110,35], 
            [22,85], [22,84], [110,32], [22,74], [110,39], [22,73], [22,72], [22,79], [110,43], [22,76], [110,41], [77,109], [110,40], [22,65], [110,46], 
            [77,105], [110,51], [77,107], [110,50], [77,106], [22,68], [77,101], [110,54], [110,52], [77,96], [77,98], [110,57], [110,63], [66,54], [110,62], 
            [110,61], [66,52], [77,120], [66,51], [66,50], [110,2], [77,117], [77,116], [66,63], [110,7], [66,62], [77,118], [110,6], [66,61], [77,112], 
            [110,10], [66,57], [110,8], [77,76], [66,39], [77,79], [110,13], [77,73], [77,72], [66,35], [110,19], [110,18], [77,74], [110,17], [66,32], 
            [77,68], [66,46], [110,21], [77,65], [66,43], [66,41], [66,40], [110,24], [77,95], [110,30], [77,94], [66,21], [110,29], [110,28], [66,19], 
            [77,90], [110,98], [66,18], [77,85], [66,17], [77,84], [110,96], [77,87], [66,30], [66,29], [110,101], [66,28], [77,83], [110,107], [110,106], 
            [110,105], [66,24], [66,7], [77,46], [66,6], [77,41], [110,109], [77,40], [77,43], [66,2], [110,112], [77,39], [110,118], [66,13], [110,117], 
            [77,32], [110,116], [77,35], [66,10], [77,61], [66,8], [110,120], [55,54], [77,63], [77,62], [66,118], [55,52], [66,117], [77,57], [66,116], 
            [55,51], [55,50], [110,65], [77,52], [55,63], [66,112], [55,62], [77,54], [55,61], [110,68], [44,109], [77,51], [77,50], [55,57], [110,74], [77,13], 
            [110,73], [66,120], [55,39], [44,105], [110,72], [110,79], [44,107], [66,101], [44,106], [77,8], [55,35], [44,101], [110,76], [110,83], [77,10], 
            [66,98], [55,32], [66,96], [77,7], [55,46], [44,96], [110,87], [77,6], [66,109], [44,98], [110,85], [110,84], [55,43], [66,107], [77,2], [55,41], 
            [110,90], [66,106], [77,29], [55,40], [66,105], [77,28], [66,87], [44,120], [110,95], [77,30], [55,21], [110,94], [66,85], [77,24], [55,19], [44,117], 
            [66,84], [66,83], [55,18], [44,116], [55,17], [77,21], [44,118], [66,95], [55,30], [44,112], [66,94], [55,29], [77,17], [55,28], [77,19], [44,76], 
            [77,18], [44,79], [66,90], [55,24], [44,73], [55,7], [44,72], [55,6], [44,74], [66,68], [44,68], [55,2], [66,65], [44,65], [66,79], [55,13], [66,76], 
            [55,10], [66,74], [44,95], [66,73], [55,8], [44,94], [66,72], [55,118], [55,117], [44,90], [55,116], [44,85], [44,84], [44,87], [55,112], [44,83], 
            [44,46], [55,120], [44,41], [44,40], [44,43], [55,101], [55,98], [44,39], [55,96], [44,32], [44,35], [55,109], [44,61], [55,107], [55,106], [44,63], 
            [55,105], [44,62], [44,57], [55,87], [55,85], [55,84], [55,83], [44,52], [44,54], [55,95], [55,94], [44,51], [44,50], [44,13], [55,90], [44,8], 
            [44,10], [55,68], [44,7], [55,65], [44,6], [55,79], [44,2], [55,76], [44,29], [44,28], [55,74], [55,73], [44,30], [55,72], [44,24], [44,21], [44,17], 
            [44,19], [44,18], [11,35], [11,32], [11,39], [11,43], [11,41], [11,40], [11,46], [11,51], [11,50], [11,54], [11,52], [11,57], [11,63], [11,62], 
            [11,61], [11,2], [11,7], [11,6], [11,10], [11,8], [11,13], [11,19], [11,18], [11,17], [11,21], [11,24], [11,30], [11,29], [11,28], [11,98], [11,96], 
            [11,101], [11,107], [11,106], [11,105], [11,109], [11,112], [11,118], [11,117], [11,116], [11,120], [33,105], [33,107], [33,106], [33,109], [11,65], 
            [33,96], [33,98], [11,68], [33,101], [11,74], [11,73], [11,72], [11,79], [33,120], [11,76], [11,83], [11,87], [33,112], [11,85], [11,84], [33,117], 
            [33,116], [11,90], [33,118], [33,73], [11,95], [33,72], [11,94], [33,74], [33,76], [33,79], [33,65], [33,68], [33,90], [33,95], [33,94], [33,83], 
            [33,85], [33,84], [33,87], [33,41], [33,40], [33,43], [33,46], [33,32], [33,35], [33,39], [33,57], [33,61], [33,63], [33,62], [33,51], [33,50], [33,52], 
            [33,54], [33,8], [33,10], [33,13], [33,2], [33,7], [33,6], [33,24], [33,29], [33,28], [33,30], [33,17], [33,19], [33,18], [33,21], [88,24], [88,29], 
            [88,28], [88,30], [88,17], [88,19], [88,18], [88,21], [88,8], [88,10], [88,13], [88,2], [88,7], [88,6], [88,57], [88,61], [88,63], [88,62], [88,51], 
            [88,50], [88,52], [88,54], [88,41], [88,40], [88,43], [88,46], [88,32], [88,35], [88,39], [88,90], [88,95], [88,94], [88,83], [88,85], [88,84], [88,87], 
            [88,73], [88,72], [88,74], [88,76], [88,79], [88,65], [88,68], [88,120], [88,112], [99,57], [88,117], [99,63], [88,116], [99,62], [99,61], [88,118], 
            [88,105], [99,51], [99,50], [88,107], [88,106], [88,109], [99,54], [99,52], [99,43], [88,96], [99,41], [88,98], [99,40], [88,101], [99,46], [99,35], 
            [99,32], [99,39], [99,24], [99,30], [99,29], [99,28], [99,19], [99,18], [99,17], [99,21], [99,10], [99,8], [99,13], [99,2], [99,7], [99,6], [99,120], 
            [99,112], [99,118], [99,117], [99,116], [99,107], [99,106], [99,105], [99,109], [99,98], [99,96], [99,101], [99,90], [99,95], [99,94], [99,83], [99,87], 
            [99,85], [99,84], [99,74], [99,73], [99,72], [99,79], [99,76], [99,65], [99,68] }];
    end if;
    

    for i in [1..#level] do
        p:=3;
        done:=false;
        repeat
            repeat
                p:=NextPrime(p);                
                if p gt Bound then 
                    "Can't rule out rational point above j.  Increase Bound."; 
                    assert false; 
                end if; 
            until level[i] mod p ne 0 and Denominator(j) mod p ne 0 and GF(p)!j notin {GF(p)!0, GF(p)!1728};
            j0:=GF(p)!j;

            if p in Keys(trace_of_frobenius) then
                a:=trace_of_frobenius[p][j0];
            else            
                E:=EllipticCurve([ -27*j0*(j0-1728), 54*j0*(j0-1728)^2 ]);                  
                a:=TraceOfFrobenius(E);
            end if;
            
            if [a mod level[i], p mod level[i]] in trdet[i] then
                done:=true;
            end if;
        until done;
    end for;
    
    // For the smallest unentangled agreeable group, if the corresponding modular curve has only finitely many rational points,
    // then this needs to be dealt with by hand (only finitely many j have this issue!)

    if label notin Keys(X) or X[label]`genus ge 2 or X[label]`has_infinitely_many_points eq false then         
        base:=[k:k in Keys(X) | X[k]`degree eq 1][1];
        levels:=[];
        Gs:=[];
        for i in [1..#label] do
            if label[i] eq "1A0-1a" then continue i; end if;
            k:=base; 
            k[i]:=label[i];
            assert k in Keys(X);
            levels:=levels cat [X[k]`N];
            Gs:=Gs cat [X[k]`G];
        end for;
        N:=&*levels;
        Gs:=[gl2Lift(G,N): G in Gs];
        G:=&meet Gs;    
        return false, label, G;
    end if;    
      
    // We compute the rational points on the modular curve X[label] over j. 
    keys:=[label];
    k:=label;
    while X[k]`degree ne 1 do
        k:=X[k]`pi[1];
        keys:=[k] cat keys;
    end while;
    for k in keys do
        if k notin Keys(Qpoints_above_j) then
            b:=X[k]`pi[1];
            phi:=map<X[k]`C->X[b]`C | X[k]`pi[2]>;
            pts:=Qpoints_above_j[b];
            Qpoints_above_j[k]:=LiftQpoints(phi,pts);
        end if;
    end for;
    assert label in Keys(X);
    assert label in Keys(Qpoints_above_j);
 



    // Now compute the agreeable closure of G_E.  
    // We have already determined the ell-adic projections of the agreeable closure.
    keys:=unentangled_groups[label];  // sequence of agreeable groups with the correct ell-adic projections
    assert keys[1] eq label;  // should be ordered by index

    for i in [2..#keys] do

    
        k:=keys[i];
        b:=X[k]`pi[1];
        if #Qpoints_above_j[b] eq 0 then // no points to lift
            Qpoints_above_j[k]:={};  
            continue i;
        end if;
            
        // Now try to rule out rational points by traces of frobenius 
        N:=X[k]`N;
        for b in trace_of_frobenius_E do
            p:=b[1]; if N mod p eq 0 then continue b; end if;
            a:=b[2];                
            if [Integers(N)!a,Integers(N)!p] notin X[k]`trdet then
                Qpoints_above_j[k]:={};
                continue i;
            end if;
        end for;

        PolQ<w>:=PolynomialRing(Rationals());
        if X[k]`genus le 1 then
            // low genus case: lift rational points directly
            phi:=map<X[k]`C->X[b]`C | X[k]`pi[2]>;
            pts:=Qpoints_above_j[b];
            Qpoints_above_j[k]:=LiftQpoints(phi,pts);
        else
            P0:=X[k]`high_genus_model;  // We have computed a model of the high genus modular curve
            if X[b]`genus eq 1 then
                FE<x,y>:=FunctionField(X[b]`C);
                P0:=[ Evaluate(P0[2*i-1],[x,y,1])/Evaluate(P0[2*i],[x,y,1]) : i in [1..#P0 div 2]];
                if X[k]`is_serre_type_model then
                    P0[1]:=P0[1]*(j-1728);
                end if;

                Qpoints_above_j[k]:={};
                for p0 in Qpoints_above_j[b] do
                    c:=[Evaluate(a,p0): a in P0];
                    pol:=&+[c[i]*w^(i-1): i in [1..#c]];   
                    // pol gives the fiber of the model above the point p0 assuming pol is separable.
                    // We have separately dealt with all the cases where pol could be separable.
                    if HasRoot(pol) and IsSeparable(pol) then                        
                        Qpoints_above_j[k]:=Qpoints_above_j[k] join {[0]}; // we don't keep the actual point since we don't need it
                    end if;
                end for;
            else
                assert X[b]`genus eq 0;
                assert not X[k]`is_serre_type_model;
                Qpoints_above_j[k]:={};
                for p0 in Qpoints_above_j[b] do
                    if p0[2] eq 0 then continue p0; end if;  // These points have been dealt with separately in a precomputation.
                    t0:=p0[1]/p0[2];
                    c:=[Evaluate(a,t0): a in P0];
                    pol:=&+[c[i]*w^(i-1): i in [1..#c]];

                    has_root:=HasRoot(pol);
                    is_separable:=IsSeparable(pol);
                    if has_root and is_separable then          
                            Qpoints_above_j[k]:=Qpoints_above_j[k] join {[0]}; // we don't remember the actual point since we don't need it                        
                    elif has_root and is_separable eq false and j in known_exceptional_jinvariants then                    
                        Aff_<x,y>:=AffineSpace(Rationals(),2);                        
                        pol_:=&+[ Evaluate(P0[i],x)*y^(i-1): i in [1..#P0]];
                        C_:=Curve(Aff_,pol_);
                        for r in {r[1] : r in Roots(pol)} do
                            p_:=C_![t0,r];
                            if 1 in {Degree(v): v in Places(p_)} then                        
                                Qpoints_above_j[k]:=Qpoints_above_j[k] join {[0]}; // we don't remember the actual point since we don't need it   
                                break r;
                            end if;                        
                        end for;
                    end if;                    
                    // Note: we worked out all cases where the singular points may hide rationals points and added them to
                    // "known_exceptional_jinvariants", if applicable, for separate study.
                    
                end for;
            end if;

            if #Qpoints_above_j[k] ne 0 then
                return false, k, X[k]`G;                
            end if;
        end if;
    end for;


    keys:=[k: k in keys | k in Keys(Qpoints_above_j) and Qpoints_above_j[k] ne {}];  
    k:=keys[#keys]; 

    if X[k]`has_infinitely_many_points eq false then
        assert X[k]`genus eq 1;
        return false, k, X[k]`G;
    end if;

    if X[k]`is_agreeable eq false then
        // In the construction of our groups/modular curves, there are a few that are not agreeable.
        // They all have index 2 inside an agreeable group that will be the agreeable closure in this case.
        k:=X[k]`pi[1]; // will be label for agreeable closure by how X was constructed
    end if;

    // We have now found the label k for the agreeable closure of G_E!

    if minimal eq false then
        // Allow ourselves to work with a larger group that has the same commutator subgroup
        k:=X[k]`cover_with_same_commutator_subgroup;        
    end if;

    // Find points on X[k] above j-invariant j
    if k notin Keys(Qpoints_above_j) then
        phi:=X[k]`map_to_jline[1];
        S:=LiftQpoints(phi,{X[base]`C![j,1]});  
    else
        S:=Qpoints_above_j[k];
    end if;
    assert S ne {};
    
    return true, k, S;
end function;


function ComputeGammaE(k,u,E)

    /* 
        Input: 
            - a key k of our array X of modular curves corresponding to an open subgroup G of GL(2,Zhat).
              We assume X_G=X[k] has infinitely many points.   We also assume that we have chosen
              a subgroup Gc of G in the entry X[k]`Gc.  We assume other related quantities have been computed
              like the sequence of prime powers m:=X[k]`cylic_invariants.

            - u is a point of the modular curve X[k] and with respect to the computed model is not the point at infinity.

            - E is a non-CM elliptic curve whose j-invariant is the image of u under the map from X_G to the j-line.

        The rational point u and our curve E gives rise to a homomorphism 
                    gamma_E: Zhat^*-> G/Gc;
        see the paper for details.
        
        There is an isomorphism between G/Gc and the abelian group A:=AbelianGroup(m); the standard basis of A
        corresponds with the sequence X[k]`cyclic_generators of elements in G/Gc.

        Using this isomorphism, we can view gamma_E as a homomorphism Zhat^*->A.

        Output:
            - an integer M, 
            - a sequence of pairs <d,a>, where d is an integer and a is a sequence of integers with #a eq #m.

            gamma_E then factor through a homomorphism 
                    gamma: (Z/MZ)^* -> A 
            which sends each d to A!a.
    */

    BadPrimesE:=BadPrimes(E);
    L:=&*Set(BadPrimesE cat PrimeDivisors(#BaseRing(X[k]`Gc)));  

    //Check u and E are compatible
    j:=jInvariant(E);
    if [j,1] ne Eltseq((X[k]`map_to_jline[1])(u)) then
        E;
        j;
        Eltseq((X[k]`map_to_jline[1])(u));
        assert false;
    end if;

    // replace the point u by a corresponding sequence of relatively prime integers.
    u:=Eltseq(u);
    assert u[#u] ne 0; 
    c:=LCM([Denominator(a): a in u]);
    u:=[ Integers()!(c*a): a in u];
    c:=GCD(u);
    u:=[a div c : a in u];


    A<[sigma]>:=AbelianGroup(X[k]`cyclic_invariants);
    Gamma:=[];
      
    M_seq:=[]; UM_seq:=[]; iota_seq:=[];


    for i in [1..#X[k]`Gc_decomp] do
        H:=X[k]`Gc_decomp[i];    
        e:=X[k]`cyclic_invariants[i];  // exponent/cardinality of i-th cyclic group
        ContainsMinusI:=GL(2,BaseRing(H))![-1,0,0,-1] in H; // true when -I in H

        if ContainsMinusI eq false then
            Ej:=EllipticCurve([-27*j*(j-1728),54*j*(j-1728)^2]);                    

            // We find the squarefree integer d for which Ej is the quadratic twist of E by d.
            _,d1:=IsQuadraticTwist(E,Ej);
            d1:=Numerator(d1)*Denominator(d1);
            P_Ej:=Set(PrimeDivisors(GCD(Numerator(j),d1))) join Set(PrimeDivisors(GCD(Numerator(j-1728),d1))) join Set(PrimeDivisors(GCD(Denominator(j),d1)));
            d:=Sign(d1) * &*([1] cat [p: p in P_Ej | IsOdd(Valuation(d1,p)) ]);
            assert IsSquare(d*d1);
        end if;

        // We are going to construct a homomorphism from the group Z_L^*/(Z_L^*)^e.
        // We can replace M by the level of (Z_L^*)^e in GL(1,Z_L)=Z_L^*.
        M:=1;
        for p in PrimeDivisors(L) do
            if GCD(p,e) eq 1 and GCD(p-1,e) ne 1 then  // (Z_p^*)^e=Z_p^* case
                M:=M*p;
            elif GCD(p,e) ne 1 then
                // e is a positive power of p
                M:=M*e*p; 
                if p eq 2 then M:=M*2; end if;
            end if;
        end for;                

        ZM:=Integers(M);
        UM,iotaM:=UnitGroup(ZM); // unit group of Z_M
        U:=sub<UM|[]>;

        pairs:=[];
        for j in [1..Ngens(UM)] do
            g:=e*UM.j;
            if g notin U then
                U:=sub<UM|Generators(U) join {g}>;
                pairs:=pairs cat [<g,A!0>]; 
            end if;
        end for;
        // the first coordinates of elements in "pairs" generate the e-th power of (Z/MZ)^* (and are all distinct and not 1)
    
        // We have some Frobenius info precomputed.
        good_primes:= Sort([m[2]: m in Keys(cyclic_frobenius[k]) | m[1] eq i]);     

        done:=false;       
        p:=3;
        while not done or p lt prime_bound do       
            good_p:=false;

            repeat
                p:=NextPrime(p);
                // want prime p not dividing the level of our groups, want E to have good reduction at p, want p not dividing d,
                // want reduciton modulo p of our point u to make sense.
            until L mod p ne 0 and u[#u] mod p ne 0 and (ContainsMinusI or d mod p ne 0); 

            u_:=[GF(p)!(a/u[#u]): a in u];

            if p le prime_bound and [i,p] in Keys(cyclic_frobenius[k]) then
                b:=exists(f){f: f in [0..e-1] |<u_,f> in cyclic_frobenius[k][[i,p]]};                
                if b then 
                    good_p:=true;  
                end if;
            elif p gt prime_bound and not done then
                // Computes extra values if the precomputed Frobenius data is insuffcient.

                s:=ComputeFrobData(k,i, p : pt:=u_); 
                if #s ne 0 then
                    good_p:=true;
                    f:=Rep(s)[2];
                end if;
            end if;

            if good_p and not ContainsMinusI and KroneckerSymbol(d, p ) eq -1 then 
                f:=(f + (e div 2)) mod e;  
            end if;

            if not done and good_p then
                
                if p @@ iotaM notin U then 
                    U:=sub<UM|Generators(U) join {p @@ iotaM}>;
                    pairs:=pairs cat [< p @@ iotaM, f*sigma[i]>];
                end if;
                                
                if U eq UM then 
                
                    //We now define the homomorphism UM->A from the sequence of pairs "pairs"
                    FA:=FreeAbelianGroup(#pairs); 
                    iota:=hom<FA->UM | [UM!a[1]: a in pairs]>;
                    gamma_:=hom<FA->A | [a[2]: a in pairs]>;
                    gamma :=hom<UM->A | [gamma_(UM.i @@ iota) : i in [1..Ngens(UM)]]>;

                    done:=true;                   
                end if;   
                          
            elif done and good_p then
                assert gamma( p @@ iotaM) eq f*sigma[i];
            end if;

        end while;
    
        M_seq:=M_seq cat [M];
        UM_seq:=UM_seq cat [UM];
        iota_seq:=iota_seq cat [iotaM];

        Gamma:=Gamma cat [gamma];
    end for;


    // Add to get a single homomorphism gamma
    M:=LCM(M_seq);
    UM,iotaM:=UnitGroup(Integers(M));
    
    Gamma_:=[];
    for j in [1..#Gamma] do
        M_:=M_seq[j];
        U_:=UM_seq[j];
        iota_:=iota_seq[j];
        
        gamma:=hom<UM->A | x:->  Gamma[j]( (Integers(M_)!iotaM(x)) @@ iota_ )>; 
        Gamma_:=Gamma_ cat [gamma];
    end for;
    Gamma:=Gamma_;

    gamma:=hom<UM->A | [  &+[gamma(UM.i): gamma in Gamma] : i in [1..Ngens(UM)]]  >;
    // memory leak?
    
    // We have a homomorphism gamma:(Z/MZ)^*->A.  
    // We now replace M by a proper divisor so the kernel of gamma has level M.
    ker_gamma:=Kernel(gamma);  // subgroup of (Z/M)^*
    primes:=PrimeDivisors(M);
    for p in primes do
        done:=false;
        while not done do
            if GCD(M,p) eq 1 then continue p; end if;
            m:=M div p;  // does gamma factor through (Z/mZ)^*?; if so replace gamma

            Um,iotam:=UnitGroup(Integers(m));
            redm:=hom<UM->Um | [   (Integers(m)!iotaM(UM.i)) @@ iotam : i in [1..Ngens(UM)] ] >;

            if Kernel(redm) subset ker_gamma then
                //gamma factors through (Z/mZ)^*!
                gamma:=hom<Um->A | [ gamma( Um.i @@ redm ): i in [1..Ngens(Um)]] >;
                ker_gamma:=Kernel(gamma);           
                M:=m; UM:=Um; iotaM:=iotam;
            else    
                done:=true;
            end if;
        end while;
    end for;

    gamma_pairs:=[ < Integers()!iotaM(UM.j), Eltseq(gamma(UM.j))>  :  j in [1..Ngens(UM)] ];

    return M, gamma_pairs;
end function;



function ComputeHEGenerators(k,u,E: d0:=0)
    
    /* 
        Input: 
            - a key k of our array X of modular curves corresponding to an open subgroup G of GL(2,Zhat).
              We assume X_G=X[k] has infinitely many points.   We also assume that we have chosen
              a subgroup Gc of G in the entry X[k]`Gc.  We assume other related quantities have been computed
              like the sequence of prime powers m:=X[k]`cylic_invariants.

            - u is a point of the modular curve X[k] and with respect to the computed model is not the point at infinity.

            - E is a non-CM elliptic curve whose j-invariant is the image of u under the map from X_G to the j-line.

        The rational point u and our curve E gives rise to a homomorphism 
                    gamma_E: Zhat^*-> G/Gc;
        see the paper for details.   Let HE be the subgroup of g in G such that g*Gc = gamma_E(det(g)); it is an open
        subgroup of GL(2,Zhat) with full determinant.

        Output: 
            - an integer N divisible by the level of HE,
            - a sequence of generators of the group HE; given by its image in GL(2,Z/NZ) where N is divisible by the level of HE.
              The sequence starts with generators of HE intersected with SL(2,Zhat).
        
        [If d0 is set to be a nonzero integer, which should be relatively prime to N, then instead an element of HE 
        with determinant d0 is returned. The groups get so large that this will be faster than just searching for elements in HE directly.]

    */

    
    N:=#BaseRing(X[k]`Gc);
    if X[k]`N eq 1 then
        G:=GL(2,Integers(N));
    else
        G:=gl2Lift(X[k]`G,N);
    end if;

    if G eq X[k]`Gc then  // in this case, we must have gamma_E=1
        if d0 ne 0 then
            assert exists(g){g: g in G | Determinant(g) eq d0};
            return g;
        end if;        
        return #BaseRing(G), [G.i: i in [1..Ngens(G)]]; 
    end if;


    A<[sigma]>:=AbelianGroup(X[k]`cyclic_invariants);

    M,gamma_pairs:=ComputeGammaE(k,u,E);

    UM,iotaM:=UnitGroup(Integers(M));
    FA:=FreeAbelianGroup(#gamma_pairs); 
    iota:=hom<FA->UM | [a[1] @@ iotaM: a in gamma_pairs]>;
    gamma_:=hom<FA->A | [A!a[2]: a in gamma_pairs]>;
    gamma :=hom<UM->A | [gamma_(UM.i @@ iota) : i in [1..Ngens(UM)]]>;

    assert &and [gamma(gamma_pairs[j][1] @@ iotaM) eq A!gamma_pairs[j][2] : j in [1..#gamma_pairs]];

    //    We have an isomorphism A -> G/Gc that takes the standard basis to cosets represented by the sequence X[k]`cyclic_generators.
    //    We construct a map f_A: A -> SL(2,Z) so that for each a in A,  f_A(a) modulo N
    //    lies in G and represents the coset of G/Gc corresponding to a.  

    Psi:=[];
    for i in [1..#X[k]`Gc_decomp] do
        Q,iotaQ:=quo<G|X[k]`Gc_decomp[i]>;
        assert Determinant(X[k]`cyclic_generators[i]) eq 1;
        g:=G!LiftMatrix(X[k]`cyclic_generators[i],1);
        psi:=hom<Q->A | [<iotaQ(g), sigma[i]>] >; 
        psi:=hom<G->A | [psi(iotaQ(G.i)): i in [1..Ngens(G)]]>;
        Psi:=Psi cat [psi];        
    end for;
    psi:=hom<G->A | [ &+[psi(G.i): psi in Psi] : i in [1..Ngens(G)]]>;
    H:=G meet SL(2,Integers(N));
    psi:=hom<H->A | [psi(H.i): i in [1..Ngens(H)]]>;
    assert Image(psi) eq A;
    f_A:=map<A->SL(2,Integers()) | [<a,LiftMatrix(a @@ psi,1)>: a in A]>;  
   
   

    UN,iotaN:=UnitGroup(Integers(N));  
    T:=Transversal(X[k]`Gc, sl2Lift(X[k]`Hc,#BaseRing(X[k]`Gc)));  // Note: Could precompute this if it is slow.
    assert #T eq #UN;
    // The function xi: (Z/N)^* -> Gc maps each d to a matrix in Gc with determinant d.
    xi:=map<{iotaN(d): d in UN}-> Parent([1]) | [<Determinant(t),[Integers()!a: a in Eltseq(t)]>: t in T]>;  
    // Note:  Could precompute this if it is slow.

     
    // ****** We can finally compute the image GE of rho_E^*, up to conjugacy, in GL(2,Zhat) *****
   
    N_:=LCM([N,M]);   // The level of GE will divide N_; we will give GE by its image modulo N_

    UN_,iotaN_:=UnitGroup(Integers(N_));
    GL2:=GL(2,Integers(N_));
    
    // For all d in a set of generators of (Z/N_)^*, we construct a matrix in GE with determinant d.

    S:=Generators(UN_);
    if d0 ne 0 then S:={d0 @@ iotaN_}; end if;

    gens:=[];
    for u in S do
        d:=Integers()!iotaN_(u); 

        g:=GL(2,Integers(N))! xi(Integers(N)!d); // element of Gc mod N with determinant d
        

            // Now lift g to a matrix modulo N_ with determinant d 
            m1:=&*[p^Valuation(N_,p): p in PrimeDivisors(N)];
            g1:=GL(2,Integers(m1))![Integers()!a: a in Eltseq(g)]; 
            // easy to lift g mod m1 since m1 and N have the same prime divisors

            g1:=g1 * GL(2,Integers(m1))![d/Determinant(g1),0,0,1];  
            // scale my matrix that is I mod N so that g mod m1 has determinant d

            m2:=N_ div m1;
            g1:=GL2! crt(g1,[d,0,0,1],m1,m2);  
            // matrix in GL(2,Z/N_) with determinant d and g mod N lies in G mod N
            assert Determinant(g1) eq Integers(N_)!d and ChangeRing(g1,Integers(N)) eq g ;

            g:=g1;
        
        //d1:= UM![d]; h:=GL2!f_A(gamma(d1)); 
        h:=GL2!f_A(gamma(d @@ iotaM)); 
        g:=g*h;

        if d0 ne 0 then return g; end if;

        gens:=gens cat [g];
    end for;

    
    gens:= [SL(2,Integers(N_))!g : g in X[k]`Hc_gen] cat gens;
    
    return N_, gens; 

end function;


function ComputeLevelOfImageOfGalois(GE,G,Gc)
    /* 
        This technical function is used by "FindOpenImage" below.   For a non-CM elliptic curve E/Q, that function computes a group
        GE that is conjugate in GL(2,Zhat) to the image of rho_E^*.   The group GE is given as a subgroup of GL(2,Z/M),
        where M is a multiple(!) of the level of GE.   This function returns the level of GE.
        (In all the cases considered so far, M turns out to be the level times 1, 2 or 4)

        G and Gc are open subgroups of GL(2,Zhat) so that
            - Gc is normal in G and G/Gc is abelian
            - Gc has full determinant
            - the commutator subgroup of G agrees with the intersection of Gc with SL(2,Zhat)
            - GE is a subgroup of G and they have the same commutator subgroup.

        From the paper, we find that GE is a group arising from the family of groups from the pair (G,Gc).   Using this description,
        this function finds the level.  (This function will also work if GE is the image of rho_E with G and Gc having the same
        properties)
    */

    N :=#BaseRing(GE);
    N1:=#BaseRing(Gc);  assert N1 mod #BaseRing(G) eq 0;  // We assume G and Gc are given via their minimal levels.
    levelG:=gl2Level(G); //remember for later

    G:=gl2Lift(G,N1);

    // Compute the quotient group A:=G/Gc and the quotient homorphism G->A.
    // We replace A by an isomorphic group to avoid issues in Magma.
    A_,iotaA_:=quo<G|Gc>;  // could hard code if this is slow.
    A,i_:=AbelianGroup(A_);
    iotaA:=hom<G->A | [ i_(iotaA_(G.i)) :  i in [1..Ngens(G)] ] >;

    // We lift the groups to make things easier to compare.
    q1:=&*[p^Valuation(N ,p): p in PrimeDivisors(N1)];
    q2:=&*[p^Valuation(N1,p): p in PrimeDivisors(N1)];
    q:=LCM(q1,q2);
    N:=LCM(N,q);
    N1:=LCM(N1,q);
    GE:=gl2Lift(GE,N);
    G :=gl2Lift(G ,N1);
    Gc:=gl2Lift(Gc,N1);


    U,iotaU:=UnitGroup(Integers(N));
    pairs:=[ < (Determinant(GE.i)) @@ iotaU, iotaA(ChangeRing(GE.i,Integers(N1)))> : i in [1..Ngens(GE)]];
    // We now define the homomorphism gamma: U->A from the sequence of pairs "pairs"
        FA:=FreeAbelianGroup(#pairs); 
        iota:=hom<FA->U | [U!a[1]: a in pairs]>;
        gamma_:=hom<FA->A | [a[2]: a in pairs]>;
    gamma :=hom<U->A | [gamma_(U.i @@ iota) : i in [1..Ngens(U)]]>;

    // *** The group GE will consist of those g in G for which g*Gc = gamma(det g). ***

    // The level of the kernel of gamma is a divisor of N.
    // We compute the part of this level that is relatively prime to N1.
    lev2:=1;
    for p in [p: p in PrimeDivisors(N) | N1 mod p ne 0] do
        assert p ne 2;  // We assume p is odd below; with our implementation this will always be the case.

        q:=p^Valuation(N,p);
        Uq,iotaq:=UnitGroup(Integers(q));
        iq:=hom<Uq->U|   [  CRT( [Integers()!iotaq(Uq.i),1], [q,N div q]) @@ iotaU    : i in [1..Ngens(Uq)]]>; 
        gammaq:=hom<Uq-> A |  [  gamma(iq(Uq.i)) : i in [1..Ngens(Uq)] ]>;
        
        M:=Kernel(gammaq);

        if #M eq #Uq then 
            lev_p:=0;
        else        
            lev_p:=Valuation(#Uq div #M,p) +1;
        end if;
        lev2:=lev2*p^lev_p;
    end for;

    assert N mod N1 eq 0 and GCD(N div N1, N1) eq 1;
    U1,iota1:=UnitGroup(Integers(N1));   
    i1:=hom<U1->U|   [  CRT( [Integers()!iota1(U1.i),1], [N1,N div N1]) @@ iotaU    : i in [1..Ngens(U1)]]>; 
    gamma1:=hom<U1-> A |  [  gamma(i1(U1.i)) : i in [1..Ngens(U1)] ]>;
    
    // The following is a homomorphism G->A
    function phi(g)
        return iotaA(g) - gamma1( Determinant(g) @@ iota1 );
    end function;

    // We now compute the level of the kernel of phi
    // (defining the homomorphism and kernel directly was too slow in practice)
    lev1:=1;
    for p in PrimeDivisors(N1) do
        q:=p^Valuation(N1,p);

        e:=Valuation(N1,p)-1;
        repeat
            if e lt Valuation(levelG,p) then 
                // we can stop early since the level of G divides the level of GE.
                lev1:=lev1 * p^(e+1); 
                continue p;
            end if;            

            if e ge 1 then
                S:={[1+p^e,0,0,1], [1,p^e,0,1], [1,0,p^e,1], [1,0,0,1+p^e]};
                id:=[1,0,0,1];
                S:={[ CRT([a[i],id[i]], [q, N1 div q]) : i in [1..4]] : a in S};
                S:={ GL(2,Integers(N1))!a: a in S};
                if &and{ phi(a) eq Identity(A) : a in S} eq false then
                    lev1:=lev1 * p^(e+1);
                    continue p;
                end if;
            else
                S:=Generators(GL(2,Integers(p)));
                S:={[Integers()!b: b in Eltseq(a)] : a in S};
                id:=[1,0,0,1];
                S:={[ CRT([a[i],id[i]], [q, N1 div q]) : i in [1..4]] : a in S};
                S:={ GL(2,Integers(N1))!a: a in S};
                if &and{ phi(a) eq Identity(A) : a in S} eq false then
                    lev1:=lev1 * p^(e+1);
                end if;
                continue p;
            end if;
                                
            e:=e-1;
        until false;

    end for;

    level:=lev1*lev2;
    return level;
end function;    






function FindOpenImage(E : Bound:=10^8, find_level:=true, dual:=false)
    /*
        Input:  E is a non-CM elliptic curve defined over Q.

        Let G_E be the image of rho_E in GL(2,Zhat).

        Output: 
            -   a subgroup G of GL(2,Z/NZ), where N is the level of G_E, so that the inverse image of G under the reduction modulo N map 
                GL(2,Zhat)->GL(2,Z/NZ) is conjugate to G_E in GL(2,Zhat). 
            -   the index of G_E in GL(2,Zhat).
            -   the intersection of G with SL(2,Zhat) given as a subgroup of SL(2,Z/MZ) with M>0 minimal.


        Note: There are some relevant high genus modular curves that we do not know the rational points of, but can rule out by considering 
                traces of Frobenius for many primes (for example, see the paper of Rouse-Sutherland-Zurieck-Brown).
                "Bound" gives a bound on how many primes to check up; in practice this bound is never obtained, but if it does it might 
                hint at a new exceptional rational point and a error is returned.

        If "find_level" is set to false, then N will only be a multiple of the level of G_E.   
        If "dual" is set to true, then the function works the same except now G_E is the image of the dual representation rho_E^*.     
    */

    if dual then
        G, index, H:= FindOpenImage(E : Bound:=Bound, find_level:=find_level, dual:=false);
        G:=sub<GL(2,BaseRing(G))| {Transpose(g): g in Generators(G)}>;
        H:=sub<SL(2,BaseRing(H))| {Transpose(g): g in Generators(H)}>;
        return G, index, H;
    end if;
    
    j:=jInvariant(E);
    assert j notin CM_jInvariants;  // Elliptic curve should be non-CM
    E_:=E;
    
    // Now let G_E be the transpose(!) of the image of rho_E in GL(2,Zhat).  We will compute this G_E and take the transpose as a final step.

    // The following finds an agreeable subgroup G that contains G_E and has the same commutator subgroup; 
    // it has label k in the array X and G is defined up to conjugacy in GL(2,Zhat).

    nonexceptional, k, S:=FindAgreeableClosure(j : minimal:=false);
    // The "minimal" parameter set to false means that we don't need G to be the agreeable closure of G_E.  

    
    if nonexceptional eq false and j in known_exceptional_jinvariants then
        // This covers a finite number of cases where j arises from a certain modular curve with 
        // only finitely many rational points.   We have already precomputed the image in this case (up to replacing E by a quadratic twist)

        assert exists(v){v: v in ExceptionalImages | v[1] eq j};

        //    output:=[* j, a_invariants, #BaseRing(G), [Eltseq(g): g in Generators(G)], index, #BaseRing(H), [Eltseq(g): g in Generators(H)] *];
        a_invariants:=v[2];
        E0:=EllipticCurve(v[2]);  
        assert jInvariant(E0) eq j;
        _,d:=IsQuadraticTwist(E,E0);        

        G0:=sub<GL(2,Integers(v[3])) | v[4]>;
        index:=v[5];
        H0:=sub<SL(2,Integers(v[6])) | v[7]>;


        G0:=sub<GL(2,BaseRing(G0)) | [Transpose(G0.i): i in [1..Ngens(G0)]] >;  // image of rho_{E0}^*
        GE:=OpenImageOfTwist(E0,G0,d);  // image of rho_{E}^*
        GE:=sub<GL(2,BaseRing(GE)) | [Transpose(GE.i): i in [1..Ngens(GE)]] >;  // image of rho_{E}


        if find_level then
            G:=sub<GL(2,Integers(v[8]))| v[9]>;
            Gc:=sub<GL(2,Integers(v[10]))| v[11]>;
            level:=ComputeLevelOfImageOfGalois(GE,G,Gc);
            GE:=ChangeRing(GE,Integers(level));
        end if;


        return GE, index, H0;
    end if;


    // If the returned value "nonexceptional" is false, then we have likely stumbled across a new special j-invariant 
    // (for example, arising from an exceptional point on a modular curve).
    if nonexceptional eq false then  
        "Possible Exceptional j-invariant found and requires more study:",  j; 
        assert false; 
    end if;  

    // X[k] should have several extra quantities precomputed.
    assert X[k]`is_agreeable and assigned X[k]`Gc_decomp and assigned X[k]`cyclic_invariants;

    if X[k]`cyclic_invariants eq [] then
        // Special case where [G,G] equals the intersection of G with SL(2,Zhat).
        // In this case, G_E will equal G and we are done.  Note that by the construction of our G,
        // it will be a subgroup of GL(2,Z/NZ) where N is the level of G_E.

        G:=X[k]`G;

        H:=X[k]`Hc;
        GE:=sub<GL(2,BaseRing(G))|{Transpose(g): g in Generators(G)}>; // transpose to get image of rho_E and not rho_E^*   
        HE:=sub<SL(2,BaseRing(H))|{Transpose(g): g in Generators(H)}>;

        return GE, X[k]`commutator_index, HE;  
    end if;

    // We replace E by a quadratic twist by an integer d0.  This is useful since the twist can have less primes
    // of bad reduction.  We will need to remember this integer d0 for the end when we return to our original elliptic curve.

    E, d0:= MinimalTwist(E);
    d0 := SquarefreeFactorization(d0);  // I think there is a small memory leak in this Magma function 
    // ensure d0 is squarefree

    d1:=Numerator(d0);
    d1:=Sign(d1) * &*([1] cat [p: p in PrimeDivisors(d1) | IsOdd(Valuation(d1,p))]);
    d2:=Denominator(d0);
    d2:=Sign(d2) * &*([1] cat [p: p in PrimeDivisors(d2) | IsOdd(Valuation(d2,p))]);
    d0:=d1*d2; 
    

    assert IsMinimalModel(E); 
    BadPrimesE:=BadPrimes(E);

    // The (nonempty) set of rational points on the modular curve X[k] lying over the j-invariant j
    S:={Eltseq(P): P in S};
    // We remove the point of infinity to make some computations easier.
    S0:={P: P in S | P[#P] ne 0};  
    assert #S0 ne 0;   // We checked case by case in the precomputation that this new S0 is also nonempty

    u:=Rep(S0); // choose a point

    N1,gens1:=ComputeHEGenerators(k,u,E);

    GE:=sub<GL(2,Integers(N1)) | gens1>;

    // Earlier, we replaced E by its quadratic twist by an integer d0.
    // We now change GE to take this into account.

    ContainsMinusI:=GL(2,BaseRing(X[k]`Gc))![-1,0,0,-1] in X[k]`Gc;
    if ContainsMinusI eq false then
        GE:=OpenImageOfTwist(E,GE,d0);
    end if;

    // We already know a set of generators of GE intersected with SL(2,Zhat).
    // The following is a rather silly adjustment of the set of generators of GE; because of how things are 
    // implemented, this can sometimes greatly reduce the set of generators.
    gens:=[GE.i: i in [1..Ngens(GE)]];
    gens:=[g: g in gens | Determinant(g) ne 1];
    gens:=[GL(2,BaseRing(GE))!g: g in X[k]`Hc_gen] cat gens;
    GE:=sub<GL(2,BaseRing(GE)) | gens>;

    // We now replace GE by its image modulo its level.
    if find_level then
        if X[k]`N ne 1 then G:=X[k]`G; else G:=GL(2,Integers(2)); end if;
        level:=ComputeLevelOfImageOfGalois(GE,G,X[k]`Gc);
        GE:=ChangeRing(GE,Integers(level));
    end if;

    HE:=X[k]`Hc;

    // transpose at end!  This gives image of rho_E (not rho_E^*)
    GE:=sub<GL(2,BaseRing(GE))|{Transpose(g): g in Generators(GE)}>;
    HE:=sub<SL(2,BaseRing(HE))|{Transpose(g): g in Generators(HE)}>;

    return GE, X[k]`commutator_index, HE;
end function;


function FindLevels(G,index,H)
    /*  
        Consider a non-CM elliptic curve E/Q. 
        Input
            G, index, H:  these should be the output of FindOpenImage(E).

        Recall G is a subgroup of GL(2,Z/NZ) that describes the image of rho_E, up to conjugacy, where
        N is its level.

        Output:
            - a sequence of all pairs (d,i), ordered by increasing d, so that the image of G modulo d has 
                index i in GL(2,Z/dZ) and G modulo e has index < i in GL(2,Z/eZ) for all proper divisors e of d.
            - a sequence of the same length of the last one that describes the group obtained by taking the 
              image of G modulo d and then intersecting with SL(2,ZdZ); it is given as a pair where the first
              value is the level and thhe second is a sequence of its generators mod the level.

    */
    N:=#BaseRing(G);
    N0:=#BaseRing(H);
    H:=sl2Lift(H,N); 

    N1:=&*[p^Valuation(N,p): p in PrimeDivisors(N0)];
    N2:=N div N1;
    assert N mod N1 eq 0 and GCD(N1,N2) eq 1;

    sl2group:=AssociativeArray();
    pairs:=AssociativeArray();

    pairs[1]:=1;
    sl2group[1]:=[*1,[]*];

    for d1 in Divisors(N1) do
 
        if d1 eq 1 then 
            continue d1; 
        end if;
    
        G1:=ChangeRing(G,Integers(d1));
        H1:=ChangeRing(H,Integers(d1));
        ind1:=#GL(2,Integers(d1)) div #H1;

        HH:= G1 meet SL(2,Integers(d1));
        T:=[t: t in Transversal(HH,H1)];

        A1_,q1_:=quo<G1|H1>;
        A1,q1:=AbelianGroup(A1_);

        for d2 in Divisors(N2) do
            A2,iota2:=UnitGroup(Integers(d2));
            A,i1,i2:=DirectSum(A1,A2);

            function phi(g,e)
                return i1(q1(q1_( ChangeRing(g,Integers(d1)) ))) + i2( (Integers(d2)!e) @@ iota2 );
            end function;
          
            V:=sub<A|[ phi(g,Determinant(g)) : g in Generators(G)]>;
            U:=sub<A| [phi(g,1): g in Generators(HH)]>;
            W:=U meet V;
            
            gens:=[]; W0:=sub<A|gens>;            
            gens_:=[t: t in Generators(H1)];
            T0:=T;
            while W0 ne W do   
                t:=T0[#T0];  Prune(~T0);
                w:=phi(t,1);
                if w in W and w notin W0 then
                    gens:=gens cat [w];
                    gens_:=gens_ cat [t];
                    W0:=sub<A|gens>;
                end if;
            end while;
            
            H_:=sub<HH|gens_>;
            assert Index(H_,H1) eq #W;

            N_:=sl2Level(H_);
            if N_ eq 1 then
                sl2group[d1*d2]:=[*1,[]*];
            else
                H_:=ChangeRing(H_,Integers(N_));
                sl2group[d1*d2]:=[*N_,[ [Integers()!b: b in Eltseq(g)] : g in Generators(H_) ]*];
            end if;

            ind2:=EulerPhi(d2);
            pairs[d1*d2]:= (ind1*ind2) div #V;

        end for;
    end for;

    D:={d: d in Keys(pairs) |  d ne 1 and &and{ pairs[d] ne pairs[e] : e in Divisors(d) | e in Keys(pairs) and e ne d}  };
    D:=D join {1};
    D:=Sort([d: d in D]);

    pairs0:=[[d,pairs[d]]: d in D];
    groups:=[sl2group[d]: d in D];

    return pairs0, groups;
end function;
