Section Berardi.
  Hypothesis EM : forall P : Prop, P \/ ~P.

  Variables (Bool : Prop) (T F : Bool).

  Record fpair (A B : Prop) := {
      fp_f : A -> B;
      fp_g : B -> A
    }.
  Arguments fp_f {A B}.
  Arguments fp_g {A B}.

  Definition is_retract {A B} (fp : fpair A B) := forall x, fp_g fp (fp_f fp x) = x.

  Record retract (A B : Prop) := { retr_pair : fpair A B; retr_prf : is_retract retr_pair }.

  Definition pow (X : Prop) := X -> Bool.

  Definition empty_set {X : Prop} : pow X := fun _ => F.

  Definition make_retract (A B : Prop) : fpair (pow A) (pow B) :=
    match EM (retract (pow A) (pow B)) with
    | or_introl retract => retr_pair _ _ retract
    | or_intror _ => {| fp_f := fun _ => empty_set; fp_g := fun _ => empty_set |}
    end.

  Lemma make_retract_spec {A B : Prop} : retract (pow A) (pow B) -> is_retract (make_retract A B).
  Proof.
    unfold make_retract.
    destruct EM as [[] |]; tauto.
  Qed.

  Definition U : Prop := forall X : Prop, pow X.

  Definition embed_to_U (X : Prop) := make_retract X U.

  Definition inj_U (f : pow U) : U := fun X => fp_g (embed_to_U X) (fp_f (embed_to_U U) f).
  Definition proj_U (u : U) : pow U := u U.
  Definition emb_U := {| fp_f := inj_U; fp_g := proj_U |}.
  Lemma emb_U_retract : is_retract emb_U.
  Proof.
    unfold is_retract, emb_U. simpl.
    intro x.
    unfold inj_U, proj_U.
    unfold embed_to_U.
    rewrite make_retract_spec; auto.
    now exists {| fp_f x := x; fp_g x := x |}.
  Qed.

  Definition IFTE (P : Prop) {Q : Prop} (x y : Q) : Q :=
    match EM P with
    | or_introl _ => x
    | or_intror _ => y
    end.

  Lemma IFTE_t : forall (P : Prop) {Q : Prop} (x y : Q), P -> IFTE P x y = x.
  Proof.
    intros.
    unfold IFTE.
    destruct (EM P); tauto.
  Qed.

  Lemma IFTE_f : forall (P : Prop) {Q : Prop} (x y : Q), ~P -> IFTE P x y = y.
  Proof.
    intros.
    unfold IFTE.
    destruct (EM P); tauto.
  Qed.

  Definition mem (u v : U) := fp_g emb_U v u = T.
  Definition RUSSEL : pow U := fun r => IFTE (~mem r r) T F.
  Definition r := fp_f emb_U RUSSEL.


  Lemma mem_r_r : mem r r = (IFTE (~mem r r) T F = T).
  Proof.
    unfold mem at 1, r at 1.
    now rewrite emb_U_retract.
  Qed.

  Theorem proof_irrelevance : F = T.
  Proof.
    destruct (EM (mem r r)) as [Hmem | Hnmem].
    - generalize Hmem.
      now rewrite mem_r_r, IFTE_f.
    - absurd (T = T); auto.
      generalize Hnmem.
      now rewrite mem_r_r, IFTE_t.
  Qed.
End Berardi.
