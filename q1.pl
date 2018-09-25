% ^ denotes and operator
% + denotes or operator
% < denotes implication operator
% > denotes biconditional operator
% - denotes negation operator
% Query solve((p + -q) ^ (q ^ -r) ^ (r < p)).
% solve(-(p < (q < p))).


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

tableau(X) :- T = tree( _, _, [X],empty,empty), solver(T).

solver(X) :- extend_tree(X), print_tree(X),!.

print_tree(X):-  write_tree(X,Y,Z),check_if_number(Y,Z),((Y>0,Z<1) -> writeln(""),write("Inconsistent");((Y>0,Z>0) -> writeln(""),write("Consistent"); writeln(""),write("Valid"))).

check_if_number(Y,Z):- number(Y), number(Z),!.
check_if_number(Y,Z):- number(Y), Z is 0,!.
check_if_number(Y,Z):- number(Z), Y is 0.

extend(Left,Right):- extend_tree(Left),!, extend_tree(Right),!.

create_node(X,Y,P,Q) :- X = tree(_,_,Y,P,Q).

create_nodes(W,X,Y,Z,P,Q):- W=tree(_,_,X,P,Q), Y=tree(_,_,Z,P,Q).

ifmemberthendelete(A,L,Ltemp,Q):-  mem(A,L),Q = A, del(L,A, Ltemp).

assignnegation(A,A1," ~~a ") :- A = - - A1.

orrules(L, [B1 | LT], [B2 | LT],P,Q) :- orformula(B1,B2,B,P), ifmemberthendelete(B,L,LT,Q).

orformula( A1, A2, A1 + A2, " (a v b) ").
orformula( - (- A1 + A2), - (- A2 + A1), - (A1 > A2), " ~(a <-> b)").
orformula( - A1, A2, A1 < A2, " (a -> b) ").
orformula( - A1, - A2, - (A1 ^ A2), " ~ (a ^ b) ").


andrules(L, [A1, A2 | LT],P,Q) :- andformula(A1,A2, A,P), ifmemberthendelete(A,L,LT,Q).
andrules(L, [A1 | LT], P,Q) :- assignnegation(A,A1,P), ifmemberthendelete(A,L,LT,Q).

andformula( A1, - A2, - (A1 < A2), " ~(a -> b) ").
andformula( A1, A2, A1 ^ A2, " (a ^ b) ").
andformula(  - A1 + A2,  - A2 + A1, A1 > A2, " (a <-> b) ").
andformula( - A1,  - A2, - (A1 + A2), " ~(a v b)").

literalsonly([]).
literalsonly([F | T]) :- atom(F), literalsonly(T).
literalsonly([-F | T]) :- atom(F), literalsonly(T).

extend_tree( tree(pathclosed, nil, L,_,_)) :- mem(F,L), mem( - F, L).
extend_tree(tree(pathopen, nil, L,_,_)) :- literalsonly(L),!.
extend_tree( tree(Left, nil, L,_,_)) :- andrules(L,L1,P,Q), create_node(Left,L1,P,Q), extend_tree(Left),!.
extend_tree(tree(Left, Right, L,_,_)) :- orrules(L,L1,L2,P,Q), create_nodes(Left,L1,Right,L2,P,Q), extend(Left, Right).

write_t([F]) :- write(F).
write_t([F | T]) :- write(F), write(","), write_t(T).

write_p(empty):-!.
write_p(X):-write("  ---> Rule " : X).

write_q(empty) :- !.
write_q(X):- write("  ---> Applied On " :  X).

check_write(Left, Right, Y, Z):- write_tree(Left, Y, Z), write_tree(Right, Y, Z).

write_tree(nil,_,_).
write_tree(pathclosed,Y,_) :- write(" ---> Closed"),Y is 1.
write_tree(pathopen,_,Z) :-  write(" ---> Open"), Z is 1.
write_tree(tree(Left, Right, List,P,Q),Y,Z) :- writeln(""), write_t(List),!,write_p(P),!,write_q(Q), check_write(Left, Right, Y, Z). 







