(* MP1 2023/2024 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

let rec l_negatif l clause =
  match clause with
  | [] -> []
  | x::reste ->
    if l=(-x) then l_negatif l reste  
    else x::l_negatif l reste
;;

(* ----------------------------------------------------------- *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let rec simplifie l clauses =
  (*  
    parcours de la liste de clauses
  *)
  match clauses with
  | [] -> []
  | x::reste ->
    (* vérifie si
       le littéral l se trouve dans la clause x
       si oui -> on n'ajoute pas la clause au
       résultat, si non -> on enlève les
       littéraux égaux à -l dans la clause et
       on ajoute la clause au résultat *)
    if List.mem l x then simplifie l reste
    else (l_negatif l x)::(simplifie l reste)
;;


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(*let () = print_modele (solveur_split exemple []) *)
(*let () = print_modele (solveur_split coloriage [])*) 

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)

let pur clauses =
  let rec pur_aux clause clauseDeBase = 
    match clause with 
    (* si clause est vide alors il n'y a pas de littéral pur*)
    | [] -> failwith "Pas de littéral pur"
    (*on vérifie le premier élément de clause*)
    | x::reste -> 
      (*si l'opposé de x n'est pas dans la clause de base alors x est pur*)
      if not(List.mem (-x) clauseDeBase) then x
      (*sinon on vérifie les éléments suivants*)
      else pur_aux reste clauseDeBase
  
  (*on appelle pur_aux avec clauses transformé en liste simple*)
  in pur_aux (List.flatten clauses) (List.flatten clauses)

(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses =
  match clauses with
  (*si clauses est vide alors il n'y a pas de clause unitaire*)
  | [] -> failwith "Not_found"
  (*on vérifie la premiere liste de clauses*)
  | x::reste ->
    (*si x est de taille 1 alors c'est une clause unitaire et on la renvoie*)
    if List.length x = 1 then List.nth x 0
    (*sinon on vérifie les liste suivantes*)
    else unitaire reste

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (*fonction qui appelle unitaire et qui renvoie le littéral s'il y a une clause unitaire et 0 sinon*)
  let uni2 clauses =
    try 
      let uni = unitaire clauses in
      uni
    with
      | _ -> 0
    (*fonction qui appelle pur et qui renvoie le littéral s'il y a un littéral pur et 0 sinon*)
  in let pur2 clauses =
    try
      let pu = pur clauses in
      pu
    with
      | _ -> 0
  in
  let rec solveur_aux clauses interpretation =
    (*si clauses est égale a [] alors clauses est satisfaisable et renvoie son interprétation*)
    if clauses = [] then Some interpretation 
    (*si clauses contient la clause vide alors c'est insatisfiable, on renvoie none*)
    else if List.mem [] clauses then None
    else
      (*on appelle uni2 et on la met dans uni*)
      let uni = uni2 clauses in
      (*si uni est différent de 0 alors il existe une clause unitaire on va donc simplifier clauses par uni et l'ajouter a la liste d'interprétation*)
      if uni <> 0 then solveur_aux (simplifie uni clauses) (uni::interpretation)
      else 
        (*on appelle pur2 et on la met dans pu*)
        let pu = pur2 clauses in
        (*si pu est différent de 0 alors il existe un littéral putr on va donc simplifier clauses par pu et l'ajouter a la liste d'interprétation*)
        if pu <> 0 then solveur_aux (simplifie pu clauses) (pu::interpretation)
        else 
          (*on créer l qui est le premier littéral de clauses*)
          let l = List.hd (List.hd clauses) in
          (*on appelle la première branche où on simplifie par l et on l'ajoute a l'interprétation*)
          let branche = solveur_aux (simplifie l clauses) (l::interpretation) in
          match branche with
          (*si la branche mène a none alors cette branche est insatisfiable on va donc appeler solveur_aux avec le littéral opposé*)
          | None -> solveur_aux (simplifie (-l) clauses) ((-l)::interpretation)
          (*sinon on renvoie la branche*)
          | _    -> branche
  in solveur_aux clauses []
  ;;

     
(*
let () =
  (* Exemple de test *)
  let l = 1 in
  let clauses = [[-1; 2; 3]; [1; -2; -3]; [-1]; [-2; 3]; [3; -4]] in
  let simplified = simplifie l clauses in
  print_list_list simplified*)

(* let () =
  (* Exemple de test *)
  let clauses = [[1; 2; 3]; [-1; 4]; [-2]; [3; -4]; [5]] in
  try
    let unit = unitaire clauses in
    print_string "Clause unitaire trouvée : ";
    print_int unit;
    print_newline ()
  with
  | Not_found -> print_string "Aucune clause unitaire trouvée";
    print_newline () *)


(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
