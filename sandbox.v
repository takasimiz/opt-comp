Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

(*FW: 
i better off at FIRST implement a variant of [taboo] called [r2l] which is neither random nor taboo, namely bruteforce,  -- otherwise you can not keep my motivation at all I bet. hence let's get started. *)

(** *Objective function *)

(** so far, [designspace] is only supported a subset of nat. *)
Definition designSpace := nat.    
Definition range := nat.
Definition objFun := designSpace -> range.
Definition ev (x:designSpace) (f:objFun) := f x.

(** *Non-randomized taboo alg. [r2l] *)
Definition r2l (f:objFun) : range :=
  (fix r2l' x xBest yBest :=
     let y := (ev x f) in
     let (xBest', yBest') := if y <? yBest then (x, y) else (xBest, yBest) in
     match x with 
       | 0   => xBest 
       | S n => r2l' n xBest' yBest'
     end) 10 10 100.

Fixpoint r2l'' f (x xBest: designSpace) (yBest : range) : designSpace :=
  let y := (ev x f) in
  let (xBest', yBest') := if y <? yBest then (x, y) else (xBest, yBest) in
  match x with 
    | 0   => xBest 
    | S n => r2l'' f n xBest' yBest'
  end.

Fixpoint r2l' f xInit := r2l'' f xInit 10 100.

Lemma defaultArgsWork: forall f, (r2l f) = (r2l' f 10).
Proof. auto. Qed.

(* Module FW__ClassInheritenceClass. *)
(* (** Fw:Org: *)
(* ------------------------------------------------------------ *)
(* * "How should I represent ∞ in Coq?" :Out:SE:  *)
(* ** "Class Inheritance" in Coq *)
(* *** I haeard at [[https://sf.com][Chapter Subtype of SF]] that, Class Inheritance in Java is akin to Subtype in coq, *)
 



 (* ------------------------------------------------------------ *)
(* *) *)
(* Print nat. *)

(* Print option. *)

(* Inductive opt (A : Type) : Type := Som : A -> opt A | Non : opt A. *)
(* Inductive opt' (A : Type) : Type := Som : A -> opt A | Non : opt A. *)

(* Inductive option__nat := Some': forall n : nat, option__nat n | None : option__nat.  *)
(* Inductive nat' (m : nat)  := Fin : forall m : nat,  nat' m | Inf : nat' m. *)
(* Inductive nat' : Set := O' : nat' | S' : nat' -> nat' | Inf : nat' . *)
(* Check Inf. *)
(* End FW__ClassInheritenceClass. *)

(* Definition three : nat' := 3. *)



(* Check (3 : nat'). *)
(* Definition isInf : nat' := ca  *)
(* Corollary defaultArgsWork': forall f, (r2l f) = (r2l' f infAlmost). *)
(* Proof. *)
(*   auto. *)
(* Qed.   *)


Module TEST1.
  Definition parabola : objFun := fun x => (x-2)*2.
  Check parabola.
 Compute parabola.
  Check (ev 3 parabola).
  (* ev 3 parabola *)
  (*      : range *)
  Compute (ev 3 parabola).
  (* = 6 *)
  (* : range *)
  Compute (r2l TEST1.parabola).
End TEST1.

(*FW:
 Well done! next is multi-stared xor randomized ver. well both are hard! but former is relatively easy. 

But before moving on, let's me try refoctoring: default argumenting.
*)

Module FW__DefaultArgument.
  Definition foo x y := x*y.
  Print foo.
  Definition foo2 x := x*2.
  Print foo2.
  Definition foo2' x := foo x 2.

  Theorem defaltArgumentWorks : forall x, foo2 x = foo2' x.
  Proof.
    intro.
    unfold foo2.
    unfold foo2'.
    unfold foo.
    reflexivity.
  Qed.
End FW__DefaultArgument.

(*FW:
 Making multi-started ver. is useful because, end of the day, I have to GA and SA -- both are population-based alg., namely multi started.
*)
(** **Vevify exhaustness *)
(** *[r2l__pop]: a population-based [r2l] *)
(*FW: 
well, ok, now I have to import List lib. to deal with a bunch of particles. to do so, cf. 
https://github.com/STakashimizu/ConShift/blob/master/Main.v
would be useful.
*)

Require Import Coq.Lists.List.
Import ListNotations.

Module FW__recallHowToHandleLists.
  Check [3; 4].
  Check [].
  Check ([] : list nat).
  Theorem empty_list_annotation: forall A:Type, ([] : list A) = (nil : list A).
    reflexivity.
  Qed.

  Check cons nil.
  Check cons 111 nil.
  Check cons 111 (cons 222 nil).

  Fixpoint len {A : Type} (ns: list A) : nat :=
    (fix len' ns l := match ns with
                       | nil => l
                       | cons _ ms => len' ms l+1
                     end
    ) ns 0.
  Theorem lis3: len [11; 22; 33] = 3.
    unfold len.
    simpl.
    reflexivity.
  Qed.

  (** FW: Good on us! *)
End FW__recallHowToHandleLists.

Check r2l.

Definition r2l__pop xs (f : objFun) :=
  let fix map__f xs := match xs with
                     | nil         => nil
                     | cons x' xs' => cons (f x') (map__f xs')
                   end in
  map__f xs.                      (* Refa: Find and use the built-in [map] function. *)

Theorem ifObjFunIsConvexThenAllPopsAreEndUpToMeetASamePositon: forall x x' : designSpace, forall f : objFun, (r2l f x) = (r2l f x').
