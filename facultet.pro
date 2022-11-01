domains
	list = lst(subject, mark)
	subject = string
	mark = integer
	summary_list = list*
	summary_list_list = summary_list*
	
	
	student = std(last_name, first_name, middle_name, millitary_department,summary_list)
	last_name, first_name, middle_name = string
	millitary_department = integer
	
	group = grp(faculty, specialty_code, group_number, group_structure) 
	faculty = string
	specialty_code, group_number = integer
	group_structure = student*
	group_structure_2 = group_structure*
	
	groups = group*
	ilist = integer*
	slist = string*

facts
max(integer,integer)
predicates

	nondeterm grp(faculty, specialty_code, group_number, group_structure)
	nondeterm lst(subject, mark)
	nondeterm std(last_name, first_name, middle_name, millitary_department,summary_list)
	
	nondeterm num_students_of_faculty(faculty, integer)
	nondeterm flatten2(group_structure_2,group_structure)
	nondeterm append(group_structure,group_structure,group_structure)

	
	nondeterm not_millitary_student(string)
	nondeterm all_not_millitary_students(slist)
	

	
	nondeterm counter(group_structure, integer)
	nondeterm counter(group_structure_2, integer)
	nondeterm counter(ilist, integer)
	nondeterm counter(summary_list_list, integer)
	nondeterm member(group_structure, student)
	nondeterm member(summary_list, list)

	
	nondeterm member(ilist,integer)
	nondeterm set(ilist,ilist,ilist)

	
	nondeterm group_of_subject(string,ilist)
	nondeterm student_of_subject(string,integer)
	
	nondeterm all_subjects_of_group(integer)
	nondeterm write_subjects(summary_list)
	
	nondeterm all_f(summary_list)
	nondeterm all_lists(integer,summary_list)
	nondeterm all_groups(integer,integer)
	nondeterm max_A
	nondeterm max_A_in_list(ilist)
	
	
	
	

	
clauses
 	
	lst("Math", 5).
	lst("Phisics", 4).
	lst("English", 3).
	lst("Programming", 5).
	lst("PE", 4).
	
	std("T", "D", "A", 1,[lst("Math", 5),lst("Phisics", 5),lst("English", 5)]).
	
	grp("ESR", 1212, 1, [std("a1", "D", "A", 1,[lst("Math", 5),lst("Phisics", 4),lst("English", 3)]),
	std("a2", "D", "A", 0,[lst("Math", 5),lst("Phisics", 4),lst("English", 3)]),
	std("a3", "D", "A", 1,[lst("Math", 5),lst("Phisics", 5),lst("English", 5)]),
	std("a4", "D", "A", 1,[lst("Math", 5),lst("Phisics", 4),lst("English", 3)])]).
	
	grp("ESR", 1212, 2, [std("b1", "D", "A", 1,[lst("Math", 5),lst("Phisics", 5),lst("English", 5)]),
	std("b2", "D", "A", 1,[lst("Math", 5),lst("Phisics", 4),lst("English", 5)]),
	std("b3", "D", "A", 0,[lst("Math", 5),lst("Phisics", 4),lst("English", 3)]),
	std("b4", "D", "A", 1,[lst("Math", 5),lst("Phisics", 4),lst("English", 3)])]).
	
	
	counter([],0).
	counter([_|T], X):- counter(T, X1), X = X1+1.
	
	member([H|_], H).
	member([_|H], X):- member(H, X).
	
	set([], Buff,Res):-Res=Buff.
	set([F|L],Buff,Res):-member(Buff,F),set(L,Buff,Res).
	set([F|L],Buff,Res):-not(member(Buff,F)),set(L,[F|Buff],Res).
	
	%1
	flatten2([], []) :- !.
	flatten2([L|Ls], FlatL) :-
    	!,
    	flatten2(Ls, NewLs),
    	append(L, NewLs, FlatL).
	append( [], X, X).                                   
	append( [X | Y], Z, [X | W]) :- append( Y, Z, W).     

	num_students_of_faculty(X, Y):- findall(S,grp(X, _, _,S),Stds),flatten2(Stds,S),counter(S,Y).
	%3
	all_subjects_of_group(X):-grp(_,_,X,[S|_]),S=std(_,_,_,_,L),write_subjects(L).
	write_subjects([L|T]):-L=lst(P,_),write(P),nl,write_subjects(T).
	write_subjects([L]):-L=lst(P,_),write(P),nl.
	write_subjects([]).
	
	
	
	%4
	not_millitary_student(Surname):- grp(_,_,_,Students),member(Students,std(Surname,_,_,0,_)).
	all_not_millitary_students(List):-findall(Surname,not_millitary_student(Surname),List).
	
	%5
	student_of_subject(F, Group):- grp(_,_,Group,Students),member(Students, std(_,_,_,_,L)),member(L,L1), L1 = lst(F,_).
	group_of_subject(F,Groups2):- findall(Group,student_of_subject(F, Group),Groups1),set(Groups1,[],Groups2).
	
	
	%2

	all_f([S|T]):-S=lst(_,5),!,all_f(T).
	all_f([S]):-S=lst(_,5),!.
	all_f([]).
	all_lists(Group,List):-grp(_,_,Group,Stds),member(Stds,S),S=std(_,_,_,_,List),all_f(List).
	all_groups(Group,I):-findall(X,all_lists(Group,X),List),counter(List,I).
	max(0,0).
	max_A:-findall(X,grp(_,_,X,_),AllGroups),max_A_in_list(AllGroups).
	max_A_in_list([]):-fail.
	max_A_in_list([Head|Tail]):-all_groups(Head,MAX),max(A,B), MAX>B, retract(max(A,B)), assert(max(Head,MAX)),max_A_in_list(Tail).
        max_A_in_list([Head|Tail]):-all_groups(Head,MAX),max(_,B),MAX<=B,max_A_in_list(Tail).
	
	
	
	
goal 
%group_of_subject("Math",V).
%num_students_of_faculty("ESR",X).
%all_subjects_of_group(1).
%all_not_millitary_students(X).
%max_A;max(A,B).