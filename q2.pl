% ^ denotes and operator
% + denotes or operator
% < denotes implication operator
% > denotes biconditional operator
% - denotes negation operator
% Query:- resolution((-o + h) ^ (-h + r) ^ o, -r ).
% Query:- resolution((p + q + -w) ^ (-q + r + p), p + -w + r).



:- op(41, fy, '-').
:- op(42,yfx, '^').
:- op(43,yfx, '+').
:- op(44,xfy, '<').
:- op(45,xfy, '>').

mem(_,[]):-fail.
mem(X, [X | _]).
mem(X, [_ | T]) :- mem(X,T).

append([],L,L).
append([X|L],M,[X|N]):- append(L,M,N).

del( [X | T], X, T).
del( [H | T], X, [H | T1]) :- del(T, X, T1).

isempty([]).

resolution(X, Y) :- S = X ^ -Y, clauses([S],Z),nl, (isempty(Z) -> write("Yes, Q is a logical consequence of P") ; write("Q is not a logical consequence of P")) .

create_set([],K,K).
create_set([H|T],Z,M):- mem(H,Z),!,create_set(T,Z,M).
create_set([H|T],Z,M):- append(Z,[H],P),create_set(T,P,M). 
create_set([H|L],M):- create_set(L,[H],M).

clauses(X,Z) :- andrules(X,Y),clauses(Y,Z),!.
clauses(X,Z) :- orrules(X,Y),clauses(Y,Z),!.
clauses(X,Z) :- create_set(X,T),refute(T,T,T,Z),nl, write("Resolvent " = Z).

check(H,P):- H = -P.
check(H,P):- P = -H.

resolve(_,[],F,F).
resolve([H|T],[P|Q], F, Z):- check(H,P),ifmemberthendelete(H,F,LT),ifmemberthendelete(P,LT,LP),resolve([H|T],Q, LP, Z),!.
resolve([H|T],[_|Q], F, Z):- resolve([H|T],Q, F, Z).

refute([],_,F,F).
refute([H|T],Y, F, Z):- resolve([H|T],Y,F,P), refute(T,Y,P,Z),!.



ifmemberthendelete(A,L,Ltemp):-  mem(A,L), del(L,A, Ltemp).

assignnegation(A,A1) :- A = - - A1.

orrules(L, [B1,B2 | LT]) :- orformula(B1,B2,B), ifmemberthendelete(B,L,LT).

orformula( A1, A2, A1 + A2).
orformula( - (- A1 + A2), - (- A2 + A1), - (A1 > A2)).
orformula( - A1, A2, A1 < A2).
orformula( - A1, - A2, - (A1 ^ A2)).


andrules(L, [A1, A2 | LT]) :- andformula(A1,A2, A), ifmemberthendelete(A,L,LT).
andrules(L, [A1 | LT]) :- assignnegation(A,A1), ifmemberthendelete(A,L,LT).

andformula( A1, - A2, - (A1 < A2)).
andformula( A1, A2, A1 ^ A2).
andformula(  - A1 + A2,  - A2 + A1, A1 > A2).
andformula( - A1,  - A2, - (A1 + A2)).
