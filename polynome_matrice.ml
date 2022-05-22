(*Implementation du type polynome : *)


let rec normalise p = match p with
  | [] -> []
  | t :: q -> 
    if t = 0. then normalise q
    else p;;

    
(*On suppose maintenant les polynômes normalisés*)
let deg p = List.length p -1;;
(*deg(0) = -1 pour nous ici*)


let somme p1 p2 = 
  let d = deg p1 - deg p2 in
  let rec aux1 p01 p02 = match (p01,p02) with
    | ([], _) -> []
    | (_, []) -> []
    | (t1::q1, t2::q2) -> (t1+.t2) :: aux1 q1 q2 in

    let rec aux2 p11 p12 d0 = 
      if d0 = 0 then aux1 p11 p12
      else match (p11,p12) with
        | ([],_) -> p12
        | (_,[]) -> p11
        | (t1::q1,t2::q2) -> 
          if d0 < 0 then t2 :: aux2 p11 q2 (d0+1)
          else t1 :: aux2 q1 p12 (d0-1) in

          aux2 p1 p2 d;;

          
let rec mult_scal k poly = match poly with
  | [] -> []
  | t :: q -> (t *. k) :: mult_scal k q;;


(*Cette fonction ajoute des zeros en debut de polynome pour simplifier la multiplication*)
let rec ajt0 p k l = 
  if k = 0 then p @ l
  else ajt0 p (k-1) (0.::l);;


let mult p1 p2 =
  let n = deg p1 in

  let rec aux p01 n0 = match p01 with
    | [] -> []
    | t :: q -> somme (ajt0 (mult_scal t p2) n0 []) (aux q (n0-1)) in

    normalise (aux p1 n);;


(*On utilise une evaluation avec la méthode de Horner*)
let eval poly x = 
  let n = deg poly in
  if n = -1 then 0.
  else
    
    let rec aux p s = match p with
      | [] -> s
      | t :: q -> aux q (s*.x+.t)
        in

      aux poly 0.;;
      

let deriv poly = 
  let rec aux poly n = match poly with
  | [] -> []
  | [a] -> []
  | p :: q -> n*.p :: aux q (n-.1.) in
  aux poly (float_of_int (deg poly));;


(*Debut des fonctions auxiliaires*)


let rec dicho a b poly signe precision =
  let c = (a +. b) /. 2. in
  let val_c = eval poly c in
    if abs_float (val_c) < precision then c
    else if val_c *. signe > 0. then dicho a c poly signe precision
    else dicho c b poly signe precision;;


let rec trouve_v_m poly t signe res =
  let k = t -. res in
    if eval poly k *. signe < 0. then k
    else trouve_v_m poly t signe (res*.2.);;


let rec trouve_u_m poly t signe res =
  let k = t +. res in
    if eval poly k *. signe > 0. then k
    else trouve_u_m poly t signe (res*.2.);;


let round x = 
  let k = floor x in
  if x-.k > k+.1.-.x then k+.1.
  else k;;

  
let rec arrondi poly l_racines = match l_racines with
  | [] -> []
  | t :: q -> 
    let k = round (t *. 100.) /. 100. in
      if eval poly k = 0. then k :: arrondi poly q
      else t :: arrondi poly q;;


let rec est_dans e l = match l with 
  | [] -> false
  | p :: q -> 
    if p = e then true 
    else est_dans e q;;


(*pas du tout optimale mais on concidère des petites listes ici (j'aurai pu implementer un tri_fusion...)*)
let rec suppr_doublons l = match l with
  | [] -> [] 
  | p :: q -> 
    if est_dans p q then suppr_doublons q
    else p :: suppr_doublons q;;


(*fin des fonctions auxiliaires*)


let rec racines poly precision = match (normalise poly) with
  | [] -> []
  | [a] -> []
  | [a;b] -> [-.b/.a]
  | _ -> match (racines (deriv poly) precision) with
    | [] ->
      if eval poly 1. -. eval poly 0. > 0. then 
        let borne_bas = trouve_v_m poly 0. 1. 1. in
        let borne_haut = trouve_u_m poly 0. 1. 1. in
        [dicho borne_bas borne_haut poly 1. precision]
      else 
        let borne_bas = trouve_v_m poly 0. (-.1.) 1. in
        let borne_haut = trouve_u_m poly 0. (-.1.) 1. in
        [dicho borne_bas borne_haut poly (-.1.) precision]
    | t :: q -> 

      let rec aux borne_bas racines_deriv = match racines_deriv with
        | [] ->
          if eval poly (borne_bas +. 1.) -. eval poly borne_bas > 0. then
            let m1 = eval poly borne_bas in
            if m1 > 0. then []
            else 
              let borne_haut = trouve_u_m poly borne_bas 1. 1. in
                [dicho borne_bas borne_haut poly 1. precision]
          else 
            let m1 = eval poly borne_bas in
            if m1 < 0. then []
            else 
              let borne_haut = trouve_u_m poly borne_bas (-.1.) 1. in
                [dicho borne_bas borne_haut poly (-.1.) precision]
        | t1::q1 ->
          let m1 = eval poly borne_bas in
          let m2 = eval poly t1 in
          if m1 > 0. then
            if m2 <= 0. then (dicho borne_bas t1 poly (-.1.) precision) :: aux t1 q1
            else aux t1 q1
          else 
            if m2 >= 0. then (dicho borne_bas t1 poly 1. precision) :: aux t1 q1
            else aux t1 q1 in

        if eval poly t -. eval poly (t-.1.) > 0. then 
          if eval poly t < 0. then suppr_doublons (arrondi poly (aux t q))
          else suppr_doublons (arrondi poly (aux (trouve_v_m poly t 1. 1.) (t::q)))
        else 
          if eval poly t > 0. then suppr_doublons (arrondi poly (aux t q))
          else suppr_doublons (arrondi poly (aux (trouve_v_m poly t (-.1.) 1.) (t::q)))
        ;;



(*Exemples : *)
racines [1.;3.7;1./.3.;-.5.;1.] 0.00000000001;;

racines [3.;-.4.;-.9.;3.;5.;6.] 0.0000000001;;



(*Calcul matriciel : *)


(*renvoie la sous matrice de mat, obtenue en supprimant la ligne 1 et la colonne j*)
let sous_det mat j = 
  let n = Array.length mat in
  let sous_mat = Array.make_matrix (n-1) (n-1) [] in
  let k = ref 0 in
  let l = ref 0 in
  for a = 1 to (n-1) do
    begin
      for b = 0 to (n-1) do
        if b = j then ()
        else
          (sous_mat.(!k).(!l) <- mat.(a).(b) ; l := !l + 1)
      done;
      l := 0;
      k := !k + 1
    end
  done;
  sous_mat;;


(*calcul du déterminant de mat par developpement selon la 1ere ligne*)
let rec det mat = 
  let n = Array.length mat in
  if n = 1 then mat.(0).(0)
  else
    let s = ref [] in
    for j = 0 to (n-1) do
      s := somme !s (mult (mult_scal (float_of_int (1-(j mod 2)*2)) (mat.(0).(j))) (det (sous_det mat j)))
      done;
      !s;;


let mat = [|[|[1.;4.];[2.;2.];[3.]|];[|[4.];[0.;3.];[6.]|];[|[7.];[0.];[9.]|]|];;
det mat;;


(*mat1 et mat2 carre de meme dimension*)
let somme_mat mat1 mat2 = 
  let n = Array.length mat1 in
  let p = Array.length (mat1.(0)) in
  let m = Array.make_matrix n p [] in
  for i = 0 to (n-1) do
    for j = 0 to (p-1) do
      m.(i).(j) <- somme (mat1.(i).(j)) (mat2.(i).(j)) 
    done 
  done;
  m;;


let somme_mat_scal mat1 mat2 = 
  let n = Array.length mat1 in
  let p = Array.length (mat1.(0)) in
  let m = Array.make_matrix n p 0. in
  for i = 0 to (n-1) do
    for j = 0 to (p-1) do
      m.(i).(j) <- mat1.(i).(j) +. mat2.(i).(j)
    done 
  done;
  m;;


(*mat1 et mat2 carre de meme dimension n*n, multiplication m1 * m2 (dans cet ordre)*)
let mult_mat m1 m2 = 
  let n = Array.length m1 in
  let m = Array.make_matrix n n 0. in

  let rec coef i j k res =
    if k = n then res
    else coef i j (k+1) (res +. (m1.(i).(k)) *. (m2.(k).(j))) in

    for i = 0 to (n-1) do
      for j = 0 to (n-1) do
        m.(i).(j) <- coef i j 0 0.
      done
    done;
    m;;


(*multication d'une matrice par un scalaire*)
let mult_scal_mat k mat = 
  let n = Array.length mat in
  let m = Array.make_matrix n n [] in
  for i = 0 to (n-1) do
    for j = 0 to (n-1) do
      m.(i).(j) <- mult (mat.(i).(j)) k 
    done 
  done;
  m;;


let mult_scal_mat_scal k mat = 
  let n = Array.length mat in
  let p = Array.length (mat.(0)) in
  let m = Array.make_matrix n p 0. in
  for i = 0 to (n-1) do
    for j = 0 to (p-1) do
      m.(i).(j) <- k *. mat.(i).(j)
    done 
  done;
  m;;


(*renvoie la matrice identite de taille n*)
let id n = 
  let m = Array.make_matrix n n [] in
  for i = 0 to (n-1) do
      m.(i).(i) <- [1.]
  done;
  m;;


let id_scal n =
  let m = Array.make_matrix n n 0. in
  for i = 0 to (n-1) do
      m.(i).(i) <- 1.
  done;
  m;;


let zero n = Array.make_matrix n n [];;


let zero_scal n = Array.make_matrix n n 0.;;


(*A une matrice de scalaires associe une matrice de polynomes (changement de type)*)
let traduit mat =
  let n = Array.length mat in
  let mat_poly = Array.make_matrix n n [] in
  for i = 0 to (n-1) do
    for j = 0 to (n-1) do
      mat_poly.(i).(j) <- [mat.(i).(j)]
    done
  done;
  mat_poly;;


let polynome_caract mat0 = 
  let mat = traduit mat0 in
  let n = Array.length mat in
    det (somme_mat (mult_scal_mat [1.;0.] (id n)) (mult_scal_mat [-.1.] mat));;


(*renvoie toutes les valeurs propres réelles de mat*)
let valeur_propre mat = 
  racines (polynome_caract mat) 0.00000001;;


let mat = 
  [|[|6.;5.;0.|];
  [|3.;1.;1.|];
  [|2.;0.;1.|]|];;

polynome_caract mat;;
valeur_propre mat;;


let rec dernier_suppr l = match l with
  | [] -> (0.,[])
  | [a] -> (a,[])
  | t :: q -> match dernier_suppr q with
    | (a1,b1) -> (a1, t :: b1);;


(*On utilise une evaluation avec la méthode de Horner*)
let eval_mat poly mat = 
  let n = deg poly in
  let m = Array.length mat in
    if n = -1 then zero_scal n
    else
      
      let rec aux p s = match p with
        | [] -> s
        | t :: q -> aux q (somme_mat_scal (mult_mat mat s) (mult_scal_mat_scal t (id_scal m)))
          in

        aux poly (zero_scal m);;


let inverse_matrice mat = 
  let poly0 = polynome_caract mat in
  let d,poly = dernier_suppr poly0 in
    if d = 0. then failwith "la matrice n'est pas inversible"
    else mult_scal_mat_scal (-.1./.d) (eval_mat poly mat);;


inverse_matrice mat;;



(*Vecteurs propres*)

let somme_ligne l1 l2 = 
  let n = Array.length l1 in
  let m = Array.make n 0. in
  for i = 0 to (n-1) do
      m.(i) <- l1.(i) +. l2.(i)
  done;
  m;;


let mult_scal_ligne k l = 
  let n = Array.length l in
  let m = Array.make n 0. in
  for i = 0 to (n-1) do
      m.(i) <- k *. l.(i)
  done;
  m;;


let echange_ligne i j mat = 
  let li = mat.(i) in
  mat.(j) <- mat.(j);
  mat.(i) <- li;;


let combinaison_lin a i b j mat =
  mat.(i) <- somme_ligne (mult_scal_ligne a mat.(i)) (mult_scal_ligne b mat.(j));;


(*renvoie le système decrivant E(lambda) pour une martrice m et lambda une de ses valeurs propres*)
let sys_espace_propre mat lambda =
  let n = Array.length mat in
    somme_mat_scal mat (mult_scal_mat_scal (-.lambda) (id_scal n));;
  


let trouve_pivot mat j =
  let n = Array.length mat in
  let k = ref (-1) in
  for i = 0 to (n-1) do
    if mat.(i).(j) <> 0. then (k := i)
  done;
  !k;;


(*1ere etape de l'algorithme du pivot de gauss avec mat.(i).(i) un pivot*)
let simplifie1_sys mat i =
  let n = Array.length mat in
  let pivot = mat.(i).(i) in
  for k = (i+1) to (n-1) do
    let coef2 = mat.(k).(i) in
    if coef2 <> 0. then
      combinaison_lin pivot k (-.coef2) i mat
  done;;


(*2nd etape de l'algorithme du pivot de gauss avec mat.(i).(j) un pivot*)
let simplifie2_sys mat i =
  let pivot = mat.(i).(i) in
  for k = 0 to (i-1) do
    let coef2 = mat.(k).(i) in
    if coef2 <> 0. then
      combinaison_lin pivot k (-.coef2) i mat
  done;;


(*rend unitaire toute les lignes d'une matrice deja trigonalisee*)
let simplifie3_sys mat =
  let n = Array.length mat in
  for k = 0 to (n-1) do
    let coef = mat.(k).(k) in
    if coef <> 0. then
      combinaison_lin (1./.coef) k 0. 0 mat
  done;;



let arrondi_sys mat =
  let n = Array.length mat in
  for i = 0 to (n-1) do
    if round (mat.(i).(i) *. 1000000.) /. 1000000. = 0. then mat.(i).(i) <- 0.
  done;;




let trigonalise_sys mat =
  let n = Array.length mat in
  for i = 0 to (n-1) do
    let pivot = trouve_pivot mat i in
    if pivot <> (-1) then
      begin
        echange_ligne i pivot mat;
        simplifie1_sys mat i;
        arrondi_sys mat
      end
  done;
  for i = 0 to (n-1) do
    if mat.(n-1-i).(n-1-i) <> 0. then
      simplifie2_sys mat (n-1-i)
  done;
  simplifie3_sys mat;;


(*mat a déja subit trigonalise_sys mat, on peut facilement lire les vecteurs propres*)
let trouve_vecteur_propre j mat =
  let n = Array.length mat in
  let colonne = Array.make n 0. in
  for i = 0 to (j-1) do
    colonne.(i) <- -. mat.(i).(j)
  done;
  colonne.(j) <- 1.;
  colonne;;



let print_colonne colonnes = 
  let n = Array.length (List.hd colonnes) in

  let rec aux i t =
    if i = n-1 then (print_float t.(i) ; print_string ")")
    else 
      begin 
        print_float t.(i) ; 
        print_string " , " ;
        aux (i+1) t
      end in

      let rec aux1 l = match l with
        | [] -> ()
        | [t] -> (print_string "(" ; aux 0 t)
        | t :: q -> (print_string "(" ; aux 0 t ; print_string ", " ; aux1 q) in
        
        aux1 colonnes;;



let rec affiche l1 l2 = match l1,l2 with
  | [],[] -> ()
  | t1 :: q1, t2 :: q2 -> 
    print_string "Valeur propre : "; print_float t1; print_newline ();
    print_string "Vecteurs propres associés : "; print_colonne t2; print_newline (); print_newline ();
    affiche q1 q2;;



let val_propre_vect_propre mat = 
  let n = Array.length mat in
  let l1 = valeur_propre mat in

  let rec aux l= match l with
    | [] -> []
    | t :: q ->
      let m = sys_espace_propre mat t in
      trigonalise_sys m;

      let rec aux1 j =
        if j = -1 then []
        else if m.(j).(j) = 0. then trouve_vecteur_propre j m :: (aux1 (j-1))
        else aux1 (j-1) in

        aux1 (n-1) :: (aux q) in

    let l2 = aux l1 in
    affiche l1 l2;;





let mat = 
  [|[|9.;6.;1.|];
  [|3.;1.;1.|];
  [|3.;4.;-1.|]|];;


val_propre_vect_propre mat;;


let mat1 = 
  [|[|1.5;0.5;0.5|];
  [|3.;1.;1.|];
  [|9.;3.;4.|]|];;


  val_propre_vect_propre mat1;;
