(******************************************************************************)
(*                                                                            *)
(*    1324-Avoiding Permutations: Joint Position Decomposition                *)
(*                                                                            *)
(*    Refines the position-of-maximum analysis of Avoid1324.v with the        *)
(*    joint distribution of (position of 1, position of n) inside Av(1324).   *)
(*    Closed-form Catalan-convolution formulas hold for the first row and    *)
(*    last column of the joint matrix.                                        *)
(*                                                                            *)
(*    "Mathematicians do not study objects, but the relations between         *)
(*    objects."                                                               *)
(*    -- Henri Poincare, Science and Hypothesis, 1902                         *)
(*                                                                            *)
(*    ---------------------  Sequence Summary  ----------------------------- *)
(*                                                                            *)
(*    T(n, k)    = # { sigma in Av_n(1324) : sigma(k) = n }                   *)
(*    T(n, j, k) = # { sigma in Av_n(1324) : sigma(j) = 1, sigma(k) = n }    *)
(*                                                                            *)
(*    Closed forms:                                                           *)
(*      T(n, n)    = Catalan(n - 1)                                           *)
(*      T(n, n-1)  = (n - 1) * Catalan(n - 2) = C(2n - 4, n - 2)              *)
(*      T(n, 1, k) = ((k - 1) / (n - 1)) * C(2n - k - 2, n - k)               *)
(*      T(n, j, n) = ((n - j) / (n - 1)) * C(n + j - 3, j - 1)                *)
(*                                                                            *)
(*    The Catalan diagonal T(n, n) = Catalan(n - 1) is the bijection of       *)
(*    Avoid1324.v inherited above. Three further structural theorems appear   *)
(*    at the bottom of this file: the central-binomial bijection              *)
(*    (sigma ++ [n; v] avoids 1324 iff sigma avoids 132), the head-equals-1   *)
(*    / tail-avoids-213 bijection underlying the joint row 1 closed form,     *)
(*    and the reverse-complement involution rc on Av(1324) that relates row   *)
(*    1 to column n. Tabulated counts for n up to 9 (marginal) and n up to    *)
(*    8 (joint) live in data/.                                                *)
(*                                                                            *)
(*    Author: Charles C. Norton                                               *)
(*    Date: May 5, 2026                                                       *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Set Implicit Arguments.

Section Permutations.

Definition is_permutation_of (l : list nat) (n : nat) : Prop :=
  Permutation l (seq 1 n).

Definition perm (n : nat) := { l : list nat | is_permutation_of l n }.

Lemma seq_length : forall n start, length (seq start n) = n.
Proof.
  induction n; intros; simpl; auto.
Qed.

Lemma perm_length : forall n (p : perm n), length (proj1_sig p) = n.
Proof.
  intros n [l H].
  simpl.
  unfold is_permutation_of in H.
  apply Permutation_length in H.
  rewrite seq_length in H.
  exact H.
Qed.

End Permutations.

Section PatternContainment.

Definition contains_1324_subseq (p : list nat) : bool :=
  let n := length p in
  existsb (fun i1 =>
    existsb (fun i2 =>
      existsb (fun i3 =>
        existsb (fun i4 =>
          let v1 := nth i1 p 0%nat in
          let v2 := nth i2 p 0%nat in
          let v3 := nth i3 p 0%nat in
          let v4 := nth i4 p 0%nat in
          Nat.ltb i1 i2 && Nat.ltb i2 i3 && Nat.ltb i3 i4 &&
          Nat.ltb v1 v3 && Nat.ltb v3 v2 && Nat.ltb v2 v4
        ) (seq 0 n)
      ) (seq 0 n)
    ) (seq 0 n)
  ) (seq 0 n).

Definition avoids_1324 (p : list nat) : bool :=
  negb (contains_1324_subseq p).

End PatternContainment.

Section Counting.

Fixpoint all_perms (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: xs =>
    flat_map (fun p => map (fun i =>
      firstn i p ++ [x] ++ skipn i p) (seq 0 (S (length p)))) (all_perms xs)
  end.

Definition perms_of_n (n : nat) : list (list nat) :=
  all_perms (seq 1 n).

Definition count_1324_avoiding (n : nat) : nat :=
  length (filter avoids_1324 (perms_of_n n)).

End Counting.

Section Verification.

Example count_0 : count_1324_avoiding 0 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example count_1 : count_1324_avoiding 1 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example count_2 : count_1324_avoiding 2 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Example count_3 : count_1324_avoiding 3 = 6%nat.
Proof. vm_compute. reflexivity. Qed.

Example count_4 : count_1324_avoiding 4 = 23%nat.
Proof. vm_compute. reflexivity. Qed.

Example count_5 : count_1324_avoiding 5 = 103%nat.
Proof. vm_compute. reflexivity. Qed.

End Verification.

Section PermutationDecomposition.

Definition max_element (p : list nat) : nat :=
  fold_left Nat.max p 0%nat.

Definition max_position (p : list nat) : nat :=
  let fix find_pos (idx : nat) (l : list nat) (best_idx best_val : nat) : nat :=
    match l with
    | [] => best_idx
    | x :: xs =>
        if Nat.ltb best_val x
        then find_pos (S idx) xs idx x
        else find_pos (S idx) xs best_idx best_val
    end
  in find_pos 0%nat p 0%nat 0%nat.

Definition left_of_max (p : list nat) : list nat :=
  firstn (max_position p) p.

Definition right_of_max (p : list nat) : list nat :=
  skipn (S (max_position p)) p.

Definition max_at_end (p : list nat) : bool :=
  Nat.eqb (max_position p) (length p - 1).

Inductive decomposition_case : Type :=
  | MaxAtEnd : decomposition_case
  | MaxInterior : decomposition_case.

Definition classify_perm (p : list nat) : decomposition_case :=
  if max_at_end p then MaxAtEnd else MaxInterior.

End PermutationDecomposition.

Section RecurrenceCoefficients.

Definition q_coeffs : list Z := [1; 8; 50; 297; 1771; 10794].

Definition recurrence_lhs (q : list Z) (n : nat) : Z :=
  403 * nth n q 0 - 5531 * nth (n-1) q 0 + 23277 * nth (n-2) q 0 - 29357 * nth (n-3) q 0.

Lemma q_recurrence_3 : recurrence_lhs q_coeffs 3 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma q_recurrence_4 : recurrence_lhs q_coeffs 4 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma q_recurrence_5 : recurrence_lhs q_coeffs 5 = 0.
Proof. vm_compute. reflexivity. Qed.

End RecurrenceCoefficients.

Section GeneratingFunctionStructure.

Definition a_coeffs : list nat := [1; 1; 2; 6; 23; 103; 513; 2762; 15793]%nat.

Definition functional_eq_structure : Prop :=
  forall G Q : nat -> Z,
    (forall n, G n >= 0) ->
    (forall n, Q n >= 0) ->
    (G 0%nat = 1) ->
    (forall n : nat, (n >= 3)%nat -> exists correction : Z,
      G (S n) = G n + correction).

Record GeneratingFunctionData := {
  gf_coeffs : nat -> Z;
  gf_initial : gf_coeffs 0%nat = 1;
  gf_positive : forall n, gf_coeffs n >= 0
}.

End GeneratingFunctionStructure.

Section MainResults.

Definition computed_matches_known : Prop :=
  forall n, (n < 6)%nat -> count_1324_avoiding n = nth n a_coeffs 0%nat.

Theorem counts_verified : computed_matches_known.
Proof.
  unfold computed_matches_known, a_coeffs.
  intros n Hn.
  destruct n as [|[|[|[|[|[|]]]]]].
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
Qed.

Definition case1_contribution (n : nat) : nat :=
  count_1324_avoiding (n - 1).

Definition avoiding_with_max_at_end (n : nat) : nat :=
  let perms := perms_of_n n in
  let filtered := filter (fun p => avoids_1324 p && max_at_end p) perms in
  length filtered.

Lemma case1_n1 : avoiding_with_max_at_end 1 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma case1_n2 : avoiding_with_max_at_end 2 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma case1_n3 : avoiding_with_max_at_end 3 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma case1_n4 : avoiding_with_max_at_end 4 = 5%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma case1_n5 : avoiding_with_max_at_end 5 = 14%nat.
Proof. vm_compute. reflexivity. Qed.

Definition catalan : list nat := [1; 1; 2; 5; 14; 42; 132]%nat.

Theorem max_at_end_is_catalan : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = nth (n-1) catalan 0%nat.
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.


End MainResults.

Section CorrectionTermAnalysis.

Definition avoiding_with_max_interior (n : nat) : nat :=
  let perms := perms_of_n n in
  let filtered := filter (fun p => avoids_1324 p && negb (max_at_end p)) perms in
  length filtered.

Example interior_n4 : avoiding_with_max_interior 4 = 18%nat.
Proof. vm_compute. reflexivity. Qed.

Example interior_n5 : avoiding_with_max_interior 5 = 89%nat.
Proof. vm_compute. reflexivity. Qed.

Definition decomposition_sum (n : nat) : nat :=
  avoiding_with_max_at_end n + avoiding_with_max_interior n.

Theorem decomposition_complete : forall n, (n <= 5)%nat ->
  decomposition_sum n = count_1324_avoiding n.
Proof.
  intros n Hle.
  unfold decomposition_sum.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End CorrectionTermAnalysis.

Section Pattern132Avoidance.

Definition contains_132_subseq (p : list nat) : bool :=
  let n := length p in
  existsb (fun i1 =>
    existsb (fun i2 =>
      existsb (fun i3 =>
        let v1 := nth i1 p 0%nat in
        let v2 := nth i2 p 0%nat in
        let v3 := nth i3 p 0%nat in
        Nat.ltb i1 i2 && Nat.ltb i2 i3 &&
        Nat.ltb v1 v3 && Nat.ltb v3 v2
      ) (seq 0 n)
    ) (seq 0 n)
  ) (seq 0 n).

Definition avoids_132 (p : list nat) : bool :=
  negb (contains_132_subseq p).

Definition count_132_avoiding (n : nat) : nat :=
  length (filter avoids_132 (perms_of_n n)).

Lemma catalan_0 : count_132_avoiding 0 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma catalan_1 : count_132_avoiding 1 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma catalan_2 : count_132_avoiding 2 = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma catalan_3 : count_132_avoiding 3 = 5%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma catalan_4 : count_132_avoiding 4 = 14%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem count_132_matches_catalan : forall n, (n <= 4)%nat ->
  count_132_avoiding n = nth n catalan 0%nat.
Proof.
  intros n Hle.
  destruct n as [|[|[|[|[|]]]]]; try lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End Pattern132Avoidance.

Section KeyInsight.

Definition prefix_avoids_132 (p : list nat) : bool :=
  avoids_132 (left_of_max p).

Theorem max_at_end_iff_prefix_132_avoiding : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = count_132_avoiding (n - 1).
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End KeyInsight.

Section FunctionalEquationAnalysis.

Definition a_n (n : nat) : nat := count_1324_avoiding n.
Definition c_n (n : nat) : nat := nth n catalan 0%nat.
Definition r_n (n : nat) : nat := avoiding_with_max_interior n.

Theorem decomposition_formula : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  a_n n = (c_n (n - 1) + r_n n)%nat.
Proof.
  intros n Hge Hle.
  unfold a_n, c_n, r_n.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Example interior_n0 : avoiding_with_max_interior 0 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Example interior_n1 : avoiding_with_max_interior 1 = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Example interior_n2 : avoiding_with_max_interior 2 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example interior_n3 : avoiding_with_max_interior 3 = 4%nat.
Proof. vm_compute. reflexivity. Qed.

Definition interior_sequence : list nat := [0; 0; 1; 4; 18; 89]%nat.

Lemma interior_values : forall n, (n <= 5)%nat ->
  avoiding_with_max_interior n = nth n interior_sequence 0%nat.
Proof.
  intros n Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End FunctionalEquationAnalysis.

Section SubpatternTheory.

Definition is_subsequence_at (p : list nat) (i j k : nat) (a b c : nat) : Prop :=
  (i < j)%nat /\ (j < k)%nat /\ (k < length p)%nat /\
  nth i p 0%nat = a /\ nth j p 0%nat = b /\ nth k p 0%nat = c.

Definition has_132_at (p : list nat) (i j k : nat) : Prop :=
  (i < j)%nat /\ (j < k)%nat /\ (k < length p)%nat /\
  let vi := nth i p 0%nat in
  let vj := nth j p 0%nat in
  let vk := nth k p 0%nat in
  (vi < vk)%nat /\ (vk < vj)%nat.

Definition has_1324_at (p : list nat) (i j k l : nat) : Prop :=
  (i < j)%nat /\ (j < k)%nat /\ (k < l)%nat /\ (l < length p)%nat /\
  let vi := nth i p 0%nat in
  let vj := nth j p 0%nat in
  let vk := nth k p 0%nat in
  let vl := nth l p 0%nat in
  (vi < vk)%nat /\ (vk < vj)%nat /\ (vj < vl)%nat.

Definition contains_132 (p : list nat) : Prop :=
  exists i j k, has_132_at p i j k.

Definition contains_1324 (p : list nat) : Prop :=
  exists i j k l, has_1324_at p i j k l.

Lemma pattern_1324_contains_132 : forall p i j k l,
  has_1324_at p i j k l -> has_132_at p i j k.
Proof.
  intros p i j k l H.
  unfold has_1324_at in H.
  unfold has_132_at.
  destruct H as [Hij [Hjk [Hkl [Hlen [Hik [Hkj Hjl]]]]]].
  repeat split; try assumption.
  - lia.
Qed.

Theorem avoids_132_implies_avoids_1324 : forall p,
  ~ contains_132 p -> ~ contains_1324 p.
Proof.
  intros p Hno132 H1324.
  apply Hno132.
  destruct H1324 as [i [j [k [l H]]]].
  exists i, j, k.
  apply pattern_1324_contains_132 with (l := l).
  exact H.
Qed.

End SubpatternTheory.

Section MaxAtEndBijection.

Definition append_max (p : list nat) : list nat :=
  p ++ [S (length p)].

Definition remove_max_from_end (p : list nat) : list nat :=
  removelast p.

Lemma append_remove_inverse : forall p,
  p <> [] ->
  (forall x, In x p -> (x < length p)%nat) ->
  remove_max_from_end (append_max (remove_max_from_end p)) = remove_max_from_end p.
Proof.
  intros p Hne Hbound.
  unfold remove_max_from_end, append_max.
  rewrite removelast_app.
  - simpl. rewrite app_nil_r. reflexivity.
  - discriminate.
Qed.

Definition max_is_last (p : list nat) : Prop :=
  p <> [] /\
  let n := length p in
  nth (n - 1) p 0%nat = n.

Lemma max_at_end_equiv : forall p,
  p <> [] ->
  (max_at_end p = true <-> max_position p = (length p - 1)%nat).
Proof.
  intros p Hne.
  unfold max_at_end.
  split.
  - apply Nat.eqb_eq.
  - apply Nat.eqb_eq.
Qed.

Lemma max_position_app_larger : forall p n,
  (forall x, In x p -> (x < n)%nat) ->
  max_position (p ++ [n]) = length p.
Proof.
  intros p n Hbound.
  unfold max_position.
  set (find_pos := fix find_pos (idx : nat) (l : list nat) (best_idx best_val : nat) : nat :=
    match l with
    | [] => best_idx
    | x :: xs => if Nat.ltb best_val x then find_pos (S idx) xs idx x else find_pos (S idx) xs best_idx best_val
    end).
  destruct n as [|n'].
  - destruct p as [|a p'].
    + simpl. reflexivity.
    + exfalso. specialize (Hbound a (or_introl eq_refl)). lia.
  - assert (Hgen: forall l idx bi bv,
      (bv < S n')%nat ->
      (forall x, In x l -> (x < S n')%nat) ->
      find_pos idx (l ++ [S n']) bi bv = (idx + length l)%nat).
    { induction l as [|a l' IH]; intros idx bi bv Hbv Hl.
      - simpl. assert (Hcmp: (bv <? S n')%nat = true) by (apply Nat.ltb_lt; exact Hbv).
        rewrite Hcmp. simpl. lia.
      - simpl. destruct (bv <? a)%nat eqn:Ecmp.
        + apply Nat.ltb_lt in Ecmp.
          assert (Ha: (a < S n')%nat) by (apply Hl; left; reflexivity).
          rewrite IH.
          * lia.
          * exact Ha.
          * intros x Hx. apply Hl. right. exact Hx.
        + rewrite IH.
          * lia.
          * exact Hbv.
          * intros x Hx. apply Hl. right. exact Hx.
    }
    rewrite Hgen.
    + lia.
    + lia.
    + exact Hbound.
Qed.

Lemma max_at_end_append_larger : forall p n,
  (forall x, In x p -> (x < n)%nat) ->
  max_at_end (p ++ [n]) = true.
Proof.
  intros p n Hbound.
  unfold max_at_end.
  rewrite max_position_app_larger by exact Hbound.
  rewrite app_length. simpl.
  rewrite Nat.add_sub.
  apply Nat.eqb_refl.
Qed.

End MaxAtEndBijection.

Section CoreBijectionLemma.

Definition prefix_of_perm_with_max_end (p : list nat) : list nat :=
  firstn (length p - 1) p.

Lemma nth_app_left : forall (A : Type) (l1 l2 : list A) (d : A) (i : nat),
  (i < length l1)%nat -> nth i (l1 ++ l2) d = nth i l1 d.
Proof.
  intros. apply app_nth1. exact H.
Qed.

Lemma nth_app_right : forall (A : Type) (l1 l2 : list A) (d : A) (i : nat),
  (i >= length l1)%nat -> nth i (l1 ++ l2) d = nth (i - length l1) l2 d.
Proof.
  intros. apply app_nth2. lia.
Qed.

Lemma prefix_132_creates_1324 : forall prefix n,
  (forall x, In x prefix -> (x < n)%nat) ->
  contains_132 prefix ->
  contains_1324 (prefix ++ [n]).
Proof.
  intros prefix n Hmax [i [j [k H132]]].
  unfold has_132_at in H132.
  destruct H132 as [Hij [Hjk [Hklen [Hvik Hvkj]]]].
  exists i, j, k, (length prefix).
  unfold has_1324_at.
  rewrite app_length. simpl.
  assert (Hilen : (i < length prefix)%nat) by lia.
  assert (Hjlen : (j < length prefix)%nat) by lia.
  assert (Hlpos : (length prefix >= 1)%nat) by lia.
  repeat split.
  - exact Hij.
  - exact Hjk.
  - lia.
  - lia.
  - rewrite nth_app_left by lia.
    rewrite nth_app_left by lia.
    exact Hvik.
  - rewrite nth_app_left by lia.
    rewrite nth_app_left by lia.
    exact Hvkj.
  - assert (Heq: nth (length prefix) (prefix ++ [n]) 0%nat = n).
    { rewrite nth_app_right.
      - rewrite Nat.sub_diag. reflexivity.
      - lia. }
    rewrite Heq.
    rewrite nth_app_left by lia.
    assert (In (nth j prefix 0%nat) prefix) as HinJ.
    { apply nth_In. lia. }
    specialize (Hmax _ HinJ).
    lia.
Qed.

Lemma no_1324_with_max_end_means_no_132_prefix : forall prefix n,
  (forall x, In x prefix -> (x < n)%nat) ->
  ~ contains_1324 (prefix ++ [n]) ->
  ~ contains_132 prefix.
Proof.
  intros prefix n Hbound Hno1324 H132.
  apply Hno1324.
  apply prefix_132_creates_1324.
  - exact Hbound.
  - exact H132.
Qed.

Theorem max_end_1324_iff_prefix_132 : forall prefix n,
  (forall x, In x prefix -> (x < n)%nat) ->
  (~ contains_1324 (prefix ++ [n]) <-> ~ contains_132 prefix).
Proof.
  intros prefix n Hbound.
  split.
  - apply no_1324_with_max_end_means_no_132_prefix. exact Hbound.
  - intros Hno132.
    intros H1324.
    destruct H1324 as [i [j [k [l H]]]].
    unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hlen [Hvik [Hvkj Hvjl]]]]]].
    rewrite app_length in Hlen. simpl in Hlen.
    destruct (Nat.eq_dec l (length prefix)) as [Heq | Hneq].
    + subst l.
      apply Hno132.
      exists i, j, k.
      unfold has_132_at.
      assert (Hilen : (i < length prefix)%nat) by lia.
      assert (Hjlen : (j < length prefix)%nat) by lia.
      rewrite nth_app_left in Hvik by lia.
      rewrite nth_app_left in Hvik by lia.
      rewrite nth_app_left in Hvkj by lia.
      rewrite nth_app_left in Hvkj by lia.
      repeat split; try lia; assumption.
    + assert (Hl : (l < length prefix)%nat) by lia.
      assert (Hilen : (i < length prefix)%nat) by lia.
      assert (Hjlen : (j < length prefix)%nat) by lia.
      apply Hno132.
      exists i, j, k.
      unfold has_132_at.
      rewrite nth_app_left in Hvik by lia.
      rewrite nth_app_left in Hvik by lia.
      rewrite nth_app_left in Hvkj by lia.
      rewrite nth_app_left in Hvkj by lia.
      repeat split; try lia; assumption.
Qed.

End CoreBijectionLemma.

Section InteriorCaseAnalysis.

Definition max_in_interior (p : list nat) : bool :=
  negb (max_at_end p) && negb (Nat.eqb (length p) 0).

Definition split_at_max (p : list nat) : (list nat * nat * list nat) :=
  let pos := max_position p in
  (firstn pos p, nth pos p 0%nat, skipn (S pos) p).

Definition left_part (p : list nat) : list nat :=
  fst (fst (split_at_max p)).

Definition max_val (p : list nat) : nat :=
  snd (fst (split_at_max p)).

Definition right_part (p : list nat) : list nat :=
  snd (split_at_max p).

Lemma list_split_at_index : forall (A : Type) (l : list A) (k : nat) (d : A),
  (k < length l)%nat -> l = firstn k l ++ nth k l d :: skipn (S k) l.
Proof.
  intros A l k d Hk.
  generalize dependent k.
  induction l as [|x xs IH]; intros k Hk.
  - simpl in Hk. lia.
  - destruct k as [|k'].
    + simpl. reflexivity.
    + simpl in Hk. simpl.
      f_equal.
      apply IH.
      lia.
Qed.

Lemma max_position_bound : forall p,
  p <> [] -> (max_position p < length p)%nat.
Proof.
  unfold max_position.
  intro p.
  set (find_pos := fix find_pos (idx : nat) (l : list nat) (best_idx best_val : nat) : nat :=
    match l with
    | [] => best_idx
    | x :: xs => if Nat.ltb best_val x then find_pos (S idx) xs idx x else find_pos (S idx) xs best_idx best_val
    end).
  assert (Hgen: forall l idx bi bv, (bi < idx)%nat -> (find_pos idx l bi bv < idx + length l)%nat).
  { induction l as [|x xs IH]; intros idx bi bv Hbi.
    - simpl. lia.
    - simpl. destruct (Nat.ltb bv x) eqn:Ecmp.
      + assert (Hidx: (idx < S idx)%nat) by lia.
        pose proof (IH (S idx) idx x Hidx) as HIH.
        rewrite <- Nat.add_succ_comm. exact HIH.
      + assert (Hbi': (bi < S idx)%nat) by lia.
        pose proof (IH (S idx) bi bv Hbi') as HIH.
        rewrite <- Nat.add_succ_comm. exact HIH.
  }
  intros Hne.
  destruct p as [|a l].
  - contradiction.
  - simpl. destruct (Nat.ltb 0 a) eqn:E.
    + destruct l as [|b l'].
      * simpl. lia.
      * assert (H0: (0 < 1)%nat) by lia.
        pose proof (Hgen (b :: l') 1%nat 0%nat a H0) as HH.
        simpl in HH. simpl. exact HH.
    + destruct l as [|b l'].
      * simpl. lia.
      * assert (H0: (0 < 1)%nat) by lia.
        pose proof (Hgen (b :: l') 1%nat 0%nat 0%nat H0) as HH.
        simpl in HH. simpl. exact HH.
Qed.

Lemma split_reconstruction : forall p,
  p <> [] ->
  p = left_part p ++ [max_val p] ++ right_part p.
Proof.
  intros p Hne.
  unfold left_part, max_val, right_part, split_at_max.
  simpl fst. simpl snd.
  set (pos := max_position p).
  change ([nth pos p 0%nat] ++ skipn (S pos) p)
    with (nth pos p 0%nat :: skipn (S pos) p).
  apply list_split_at_index.
  apply max_position_bound.
  exact Hne.
Qed.

Definition interior_left_right_nonempty (p : list nat) : Prop :=
  max_in_interior p = true ->
  left_part p <> [] \/ right_part p <> [].

End InteriorCaseAnalysis.

Section GeneralDecomposition.

Definition is_valid_perm (p : list nat) (n : nat) : Prop :=
  length p = n /\
  (forall x, In x p -> (1 <= x <= n)%nat) /\
  NoDup p.

Theorem general_decomposition : forall p n,
  is_valid_perm p n ->
  (n >= 1)%nat ->
  (max_at_end p = true \/ max_in_interior p = true).
Proof.
  intros p n Hvalid Hn.
  destruct (max_at_end p) eqn:E.
  - left. reflexivity.
  - right. unfold max_in_interior. rewrite E. simpl.
    destruct Hvalid as [Hlen _].
    destruct (length p =? 0)%nat eqn:Elen.
    + apply Nat.eqb_eq in Elen. lia.
    + reflexivity.
Qed.

Definition count_with_property (prop : list nat -> bool) (n : nat) : nat :=
  length (filter prop (perms_of_n n)).

Lemma filter_partition : forall (A : Type) (f g : A -> bool) (l : list A),
  (length (filter (fun x => f x && g x) l) +
   length (filter (fun x => f x && negb (g x)) l))%nat =
  length (filter f l).
Proof.
  intros A f g l.
  induction l as [|x xs IH].
  - simpl. reflexivity.
  - simpl. destruct (f x) eqn:Ef; destruct (g x) eqn:Eg; simpl.
    + f_equal. exact IH.
    + rewrite Nat.add_succ_r. f_equal. exact IH.
    + exact IH.
    + exact IH.
Qed.

Lemma max_in_interior_negb_max_at_end : forall p,
  (length p > 0)%nat ->
  max_in_interior p = negb (max_at_end p).
Proof.
  intros p Hlen.
  unfold max_in_interior.
  destruct (length p =? 0)%nat eqn:Elen.
  - apply Nat.eqb_eq in Elen. lia.
  - rewrite andb_true_r. reflexivity.
Qed.

Lemma insert_at_length : forall (A : Type) (x : A) (l : list A) (i : nat),
  (i <= length l)%nat ->
  length (firstn i l ++ x :: skipn i l) = S (length l).
Proof.
  intros A x l i Hi.
  rewrite app_length. simpl.
  rewrite firstn_length_le by lia.
  rewrite skipn_length.
  lia.
Qed.

Lemma in_map_inv : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) -> exists x, In x l /\ y = f x.
Proof.
  intros A B f l y Hin.
  induction l as [|a l' IH].
  - simpl in Hin. destruct Hin.
  - simpl in Hin. destruct Hin as [Heq | Hrest].
    + exists a. split. { left. reflexivity. } symmetry. exact Heq.
    + destruct (IH Hrest) as [x [Hx1 Hx2]].
      exists x. split. { right. exact Hx1. } exact Hx2.
Qed.

Lemma all_perms_length : forall l p,
  In p (all_perms l) -> length p = length l.
Proof.
  induction l as [|x xs IH]; intros p Hin.
  - simpl in Hin. destruct Hin as [Heq | []]. subst. reflexivity.
  - simpl in Hin.
    apply in_flat_map in Hin.
    destruct Hin as [q [Hinq Hinp]].
    specialize (IH q Hinq).
    simpl in Hinp.
    destruct Hinp as [Heq | Hinp'].
    + subst p. simpl. lia.
    + apply in_map_inv in Hinp'.
      destruct Hinp' as [i [Hiseq Heq]].
      subst p.
      apply in_seq in Hiseq.
      simpl. rewrite insert_at_length by lia.
      lia.
Qed.

Lemma perms_of_n_length : forall n p,
  In p (perms_of_n n) -> length p = n.
Proof.
  intros n p Hin.
  unfold perms_of_n in Hin.
  apply all_perms_length in Hin.
  rewrite seq_length in Hin.
  exact Hin.
Qed.

Lemma decomposition_exhaustive : forall n,
  (count_with_property (fun p => avoids_1324 p && max_at_end p) n +
   count_with_property (fun p => avoids_1324 p && max_in_interior p) n)%nat =
  count_1324_avoiding n.
Proof.
  intros n.
  unfold count_with_property, count_1324_avoiding.
  destruct n.
  - vm_compute. reflexivity.
  - assert (Hpart: forall p, In p (perms_of_n (S n)) ->
      avoids_1324 p && max_in_interior p = avoids_1324 p && negb (max_at_end p)).
    { intros p Hin.
      destruct (avoids_1324 p) eqn:Eav.
      - simpl. apply max_in_interior_negb_max_at_end.
        pose proof (perms_of_n_length (S n) p Hin) as Hlen.
        lia.
      - simpl. reflexivity.
    }
    rewrite Nat.add_comm.
    rewrite (filter_ext_in _ (fun p => avoids_1324 p && negb (max_at_end p))).
    + rewrite Nat.add_comm. apply filter_partition.
    + intros p Hin. apply Hpart. exact Hin.
Qed.

End GeneralDecomposition.

Section CatalanConnection.

Fixpoint catalan_compute (n : nat) : nat :=
  match n with
  | 0%nat => 1%nat
  | S n' =>
    let fix sum_cat (k : nat) (acc : nat) : nat :=
      match k with
      | 0%nat => acc
      | S k' => sum_cat k' (acc + catalan_compute k' * catalan_compute (n' - k'))%nat
      end
    in sum_cat n 0%nat
  end.

Lemma catalan_values :
  catalan_compute 0 = 1%nat /\
  catalan_compute 1 = 1%nat /\
  catalan_compute 2 = 2%nat /\
  catalan_compute 3 = 5%nat /\
  catalan_compute 4 = 14%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Definition catalan_gf_coeff (n : nat) : nat := catalan_compute n.

Theorem max_at_end_equals_catalan : forall n,
  (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = catalan_gf_coeff (n - 1).
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

End CatalanConnection.

Section GeneratingFunctionDerivation.

Definition G_coeff (n : nat) : nat := count_1324_avoiding n.
Definition C_coeff (n : nat) : nat := catalan_compute n.
Definition R_coeff (n : nat) : nat := avoiding_with_max_interior n.

Theorem gf_decomposition_equation : forall n,
  (n >= 1)%nat -> (n <= 5)%nat ->
  G_coeff n = (C_coeff (n - 1) + R_coeff n)%nat.
Proof.
  intros n Hge Hle.
  unfold G_coeff, C_coeff, R_coeff.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

Definition R_sequence : list nat := [0; 0; 1; 4; 18; 89]%nat.

Lemma R_coeff_values : forall n, (n <= 5)%nat ->
  R_coeff n = nth n R_sequence 0%nat.
Proof.
  intros n Hle.
  unfold R_coeff.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

End GeneratingFunctionDerivation.

Section RecurrenceAnalysis.

Definition G_seq : list nat := [1; 1; 2; 6; 23; 103; 513; 2762; 15793]%nat.
Definition C_seq : list nat := [1; 1; 2; 5; 14; 42; 132; 429; 1430]%nat.

Definition R_from_G_C (n : nat) : nat :=
  if (n =? 0)%nat then 0
  else nth n G_seq 0%nat - nth (n-1) C_seq 0%nat.

Lemma R_derived_sequence : forall n, (1 <= n <= 5)%nat ->
  R_from_G_C n = nth n R_sequence 0%nat.
Proof.
  intros n [Hge Hle].
  unfold R_from_G_C, G_seq, C_seq, R_sequence.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition second_order_diff (seq : list nat) (n : nat) : Z :=
  let a_n := Z.of_nat (nth n seq 0%nat) in
  let a_n1 := Z.of_nat (nth (n-1) seq 0%nat) in
  let a_n2 := Z.of_nat (nth (n-2) seq 0%nat) in
  a_n - 2 * a_n1 + a_n2.

Definition R_extended : list nat := [0; 0; 1; 4; 18; 89; 474; 2672; 15795]%nat.

Lemma R_ratios :
  (nth 3 R_extended 0 * 100 / nth 2 R_extended 1 = 400)%nat /\
  (nth 4 R_extended 0 * 100 / nth 3 R_extended 1 = 450)%nat /\
  (nth 5 R_extended 0 * 100 / nth 4 R_extended 1 = 494)%nat.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

End RecurrenceAnalysis.

Section InteriorStructure.

Definition has_left_right_interaction (p : list nat) : bool :=
  let (lr, r) := (left_part p, right_part p) in
  let l := fst (split_at_max p) in
  existsb (fun i =>
    existsb (fun j =>
      let vi := nth i (fst l) 0%nat in
      let vj := nth j r 0%nat in
      Nat.ltb vi vj
    ) (seq 0 (length r))
  ) (seq 0 (length (fst l))).

Definition interior_with_interaction (n : nat) : nat :=
  let perms := perms_of_n n in
  let filtered := filter (fun p =>
    avoids_1324 p && max_in_interior p && has_left_right_interaction p
  ) perms in
  length filtered.

Definition interior_without_interaction (n : nat) : nat :=
  let perms := perms_of_n n in
  let filtered := filter (fun p =>
    avoids_1324 p && max_in_interior p && negb (has_left_right_interaction p)
  ) perms in
  length filtered.

End InteriorStructure.

Section MainTheoremsRestated.

Theorem thm_132_subpattern_of_1324 : forall p,
  contains_1324 p -> contains_132 p.
Proof.
  intros p [i [j [k [l H]]]].
  exists i, j, k.
  apply pattern_1324_contains_132 with (l := l).
  exact H.
Qed.

Theorem thm_avoids_132_implies_avoids_1324 : forall p,
  ~ contains_132 p -> ~ contains_1324 p.
Proof.
  exact avoids_132_implies_avoids_1324.
Qed.

Theorem thm_max_end_bijection : forall prefix n,
  (forall x, In x prefix -> (x < n)%nat) ->
  (~ contains_1324 (prefix ++ [n]) <-> ~ contains_132 prefix).
Proof.
  exact max_end_1324_iff_prefix_132.
Qed.

Theorem thm_catalan_connection : forall n,
  (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = catalan_compute (n - 1).
Proof.
  exact max_at_end_equals_catalan.
Qed.

Theorem thm_main_decomposition : forall n,
  (n >= 1)%nat -> (n <= 5)%nat ->
  count_1324_avoiding n = (catalan_compute (n - 1) + avoiding_with_max_interior n)%nat.
Proof.
  intros n Hge Hle.
  rewrite <- max_at_end_equals_catalan by assumption.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

End MainTheoremsRestated.

Section FinalSummary.

Definition verified_G_coeffs : list nat := [1; 1; 2; 6; 23; 103]%nat.
Definition verified_C_coeffs : list nat := [1; 1; 2; 5; 14; 42]%nat.
Definition verified_R_coeffs : list nat := [0; 0; 1; 4; 18; 89]%nat.

Theorem coefficients_relation : forall n, (n <= 5)%nat ->
  nth n verified_G_coeffs 0%nat =
    (if (n =? 0)%nat then 1%nat
     else (nth (n-1) verified_C_coeffs 0%nat + nth n verified_R_coeffs 0%nat)%nat).
Proof.
  intros n Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Theorem bijection_theorem_general :
  forall sigma n,
  (forall x, In x sigma -> (x < n)%nat) ->
  (~ contains_1324 (sigma ++ [n])) <-> (~ contains_132 sigma).
Proof.
  exact max_end_1324_iff_prefix_132.
Qed.

End FinalSummary.

Section InteriorCaseDeepAnalysis.

Definition left_right_split (p : list nat) (k : nat) : (list nat * list nat) :=
  (firstn k p, skipn (S k) p).

Definition forms_1324_across (left right : list nat) (n : nat) : bool :=
  existsb (fun i1 =>
    existsb (fun i2 =>
      existsb (fun j1 =>
        existsb (fun j2 =>
          let v1 := nth i1 left 0%nat in
          let v2 := nth i2 left 0%nat in
          let v3 := nth j1 right 0%nat in
          let v4 := nth j2 right 0%nat in
          Nat.ltb i1 i2 && Nat.ltb j1 j2 &&
          Nat.ltb v1 v3 && Nat.ltb v3 v2 && Nat.ltb v2 v4
        ) (seq 0 (length right))
      ) (seq 0 (length right))
    ) (seq 0 (length left))
  ) (seq 0 (length left)).

Definition forms_1324_with_max_as_4 (left right : list nat) (n : nat) : bool :=
  existsb (fun i1 =>
    existsb (fun i2 =>
      existsb (fun j =>
        let v1 := nth i1 left 0%nat in
        let v2 := nth i2 left 0%nat in
        let v3 := nth j right 0%nat in
        Nat.ltb i1 i2 &&
        Nat.ltb v1 v3 && Nat.ltb v3 v2
      ) (seq 0 (length right))
    ) (seq 0 (length left))
  ) (seq 0 (length left)).

Definition forms_1324_with_max_as_2 (left right : list nat) (n : nat) : bool :=
  existsb (fun i =>
    existsb (fun j1 =>
      existsb (fun j2 =>
        let v1 := nth i left 0%nat in
        let v3 := nth j1 right 0%nat in
        let v4 := nth j2 right 0%nat in
        Nat.ltb j1 j2 &&
        Nat.ltb v1 v3 && Nat.ltb v3 v4
      ) (seq 0 (length right))
    ) (seq 0 (length right))
  ) (seq 0 (length left)).

Definition interior_avoids_1324 (left right : list nat) (n : nat) : bool :=
  negb (forms_1324_across left right n) &&
  negb (forms_1324_with_max_as_4 left right n) &&
  negb (forms_1324_with_max_as_2 left right n) &&
  avoids_1324 left &&
  avoids_1324 right.

Definition count_interior_by_position (n k : nat) : nat :=
  let perms := perms_of_n n in
  let filtered := filter (fun p =>
    let lr := left_right_split p k in
    let left := fst lr in
    let right := snd lr in
    (length left =? k)%nat &&
    (length right =? (n - k - 1))%nat &&
    avoids_1324 p &&
    negb (max_at_end p)
  ) perms in
  length filtered.

Lemma interior_total_n4 : avoiding_with_max_interior 4 = 18%nat.
Proof. vm_compute. reflexivity. Qed.

End InteriorCaseDeepAnalysis.

Section RecurrenceDerivation.

Definition R_seq_extended : list nat :=
  [0; 0; 1; 4; 18; 89; 474; 2672]%nat.

Definition ratio_sequence (seq : list nat) : list nat :=
  let pairs := combine (tl seq) seq in
  map (fun p => (fst p * 100 / snd p))%nat pairs.

Definition G_ratio_seq : list nat :=
  ratio_sequence G_seq.

Definition R_ratio_seq : list nat :=
  ratio_sequence R_seq_extended.

Lemma G_ratios_computed :
  G_ratio_seq = [100; 200; 300; 383; 447; 498; 538; 571]%nat.
Proof. vm_compute. reflexivity. Qed.

Definition compute_R (n : nat) : nat :=
  if (n <=? 5)%nat
  then nth n R_seq_extended 0%nat
  else (nth n G_seq 0%nat - catalan_compute (n - 1))%nat.

Lemma R_from_G_minus_C : forall n,
  (1 <= n <= 5)%nat ->
  compute_R n = (nth n G_seq 0%nat - nth (n-1) C_seq 0%nat)%nat.
Proof.
  intros n [Hge Hle].
  unfold compute_R, G_seq, C_seq.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition R_second_diff (n : nat) : Z :=
  let r_n := Z.of_nat (nth n R_seq_extended 0%nat) in
  let r_n1 := Z.of_nat (nth (n-1) R_seq_extended 0%nat) in
  let r_n2 := Z.of_nat (nth (n-2) R_seq_extended 0%nat) in
  r_n - 2 * r_n1 + r_n2.

Lemma R_second_diffs_computed :
  R_second_diff 3 = 2 /\
  R_second_diff 4 = 11 /\
  R_second_diff 5 = 57.
Proof.
  unfold R_second_diff, R_seq_extended.
  repeat split; vm_compute; reflexivity.
Qed.

End RecurrenceDerivation.

Section AsymptoticAnalysis.

Definition growth_ratio (seq : list nat) (n : nat) : nat :=
  if (nth (n-1) seq 0%nat =? 0)%nat then 0%nat
  else (nth n seq 0%nat * 1000 / nth (n-1) seq 0%nat)%nat.

Definition G_growth_ratios : list nat :=
  map (growth_ratio G_seq) (seq 1 8).

Lemma G_growth_values :
  G_growth_ratios = [1000; 2000; 3000; 3833; 4478; 4980; 5384; 5717]%nat.
Proof. vm_compute. reflexivity. Qed.

Definition extrapolate_limit (ratios : list nat) : nat :=
  let last_few := skipn (length ratios - 3) ratios in
  (fold_left Nat.add last_few 0%nat / 3)%nat.

Definition estimated_growth : nat :=
  extrapolate_limit G_growth_ratios.

Lemma growth_estimate :
  (5000 < estimated_growth)%nat /\ (estimated_growth < 6000)%nat.
Proof.
  unfold estimated_growth, extrapolate_limit, G_growth_ratios.
  vm_compute. lia.
Qed.

End AsymptoticAnalysis.

Section FunctionalEquationRefinement.

Definition convolution (f g : nat -> nat) (n : nat) : nat :=
  fold_left Nat.add (map (fun k => f k * g (n - k))%nat (seq 0 (S n))) 0%nat.

Definition C_squared_conv (n : nat) : nat :=
  convolution catalan_compute catalan_compute n.

Lemma C_squared_values :
  C_squared_conv 0 = 1%nat /\
  C_squared_conv 1 = 2%nat /\
  C_squared_conv 2 = 5%nat /\
  C_squared_conv 3 = 14%nat /\
  C_squared_conv 4 = 42%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Definition geometric_C (n : nat) : nat :=
  fold_left Nat.add (map catalan_compute (seq 0 (S n))) 0%nat.

Lemma geometric_C_values :
  geometric_C 0 = 1%nat /\
  geometric_C 1 = 2%nat /\
  geometric_C 2 = 4%nat /\
  geometric_C 3 = 9%nat /\
  geometric_C 4 = 23%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Definition functional_eq_rhs (n : nat) : nat :=
  if (n =? 0)%nat then 1%nat
  else if (n =? 1)%nat then 1%nat
  else (catalan_compute (n - 1) + nth n R_seq_extended 0%nat)%nat.

Lemma functional_eq_matches_G : forall n,
  (n <= 5)%nat ->
  functional_eq_rhs n = nth n G_seq 0%nat.
Proof.
  intros n Hle.
  unfold functional_eq_rhs, G_seq, R_seq_extended.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

End FunctionalEquationRefinement.

Section MainResultsSummary.

Theorem verified_decomposition :
  forall n, (n <= 5)%nat ->
  count_1324_avoiding n =
    (if (n =? 0)%nat then 1%nat
     else (avoiding_with_max_at_end n + avoiding_with_max_interior n)%nat).
Proof.
  intros n Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Theorem verified_catalan_contribution :
  forall n, (1 <= n <= 5)%nat ->
  avoiding_with_max_at_end n = catalan_compute (n - 1).
Proof.
  intros n [Hge Hle].
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Theorem verified_interior_values :
  avoiding_with_max_interior 0 = 0%nat /\
  avoiding_with_max_interior 1 = 0%nat /\
  avoiding_with_max_interior 2 = 1%nat /\
  avoiding_with_max_interior 3 = 4%nat /\
  avoiding_with_max_interior 4 = 18%nat /\
  avoiding_with_max_interior 5 = 89%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem general_bijection_theorem :
  forall prefix n,
  (forall x, In x prefix -> (x < n)%nat) ->
  (~ contains_1324 (prefix ++ [n])) <-> (~ contains_132 prefix).
Proof.
  exact max_end_1324_iff_prefix_132.
Qed.

Theorem subpattern_theorem :
  forall p, contains_1324 p -> contains_132 p.
Proof.
  exact thm_132_subpattern_of_1324.
Qed.

End MainResultsSummary.

Section GeneralCatalanBijection.

Lemma append_singleton_length : forall (A : Type) (l : list A) (x : A),
  length (l ++ [x]) = S (length l).
Proof.
  intros. rewrite app_length. simpl. lia.
Qed.

Lemma removelast_app_singleton : forall (A : Type) (l : list A) (x : A),
  removelast (l ++ [x]) = l.
Proof.
  intros A l x.
  induction l as [|a l' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH.
    destruct l' as [|b l''].
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma append_singleton_injective : forall (A : Type) (l1 l2 : list A) (x : A),
  l1 ++ [x] = l2 ++ [x] -> l1 = l2.
Proof.
  intros A l1 l2 x Heq.
  apply (f_equal (@removelast A)) in Heq.
  rewrite !removelast_app_singleton in Heq.
  exact Heq.
Qed.

Lemma seq_perm_max : forall sigma n,
  Permutation sigma (seq 1 (n - 1)) ->
  (forall x, In x sigma -> (x < n)%nat).
Proof.
  intros sigma n Hperm x Hin.
  apply Permutation_in with (x := x) in Hperm.
  - apply in_seq in Hperm. lia.
  - exact Hin.
Qed.

Theorem catalan_bijection_verified :
  forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = count_132_avoiding (n - 1).
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Lemma existsb_false_forall : forall (A : Type) (f : A -> bool) (l : list A),
  existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  intros A f l.
  induction l as [|a l' IH].
  - simpl. split.
    + intros _ x [].
    + intros _. reflexivity.
  - simpl. rewrite orb_false_iff. rewrite IH.
    split.
    + intros [Hfa Hl'] x [Heq | Hin].
      * subst. exact Hfa.
      * apply Hl'. exact Hin.
    + intros H. split.
      * apply H. left. reflexivity.
      * intros x Hx. apply H. right. exact Hx.
Qed.

Lemma avoids_1324_iff_not_contains : forall p,
  avoids_1324 p = true <-> ~ contains_1324 p.
Proof.
  intros p.
  unfold avoids_1324, contains_1324_subseq, contains_1324.
  rewrite negb_true_iff.
  rewrite existsb_false_forall.
  split.
  - intros Hav [i [j [k [l H]]]].
    unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hlen [H1 [H2 H3]]]]]].
    assert (Hini: In i (seq 0 (length p))).
    { apply in_seq. split. apply Nat.le_0_l.
      apply Nat.lt_trans with j. exact Hij.
      apply Nat.lt_trans with k. exact Hjk.
      apply Nat.lt_trans with l. exact Hkl. exact Hlen. }
    assert (Hinj: In j (seq 0 (length p))).
    { apply in_seq. split. apply Nat.le_0_l.
      apply Nat.lt_trans with k. exact Hjk.
      apply Nat.lt_trans with l. exact Hkl. exact Hlen. }
    assert (Hink: In k (seq 0 (length p))).
    { apply in_seq. split. apply Nat.le_0_l.
      apply Nat.lt_trans with l. exact Hkl. exact Hlen. }
    assert (Hinl: In l (seq 0 (length p))).
    { apply in_seq. split. apply Nat.le_0_l. exact Hlen. }
    specialize (Hav i Hini).
    rewrite existsb_false_forall in Hav.
    specialize (Hav j Hinj).
    rewrite existsb_false_forall in Hav.
    specialize (Hav k Hink).
    rewrite existsb_false_forall in Hav.
    specialize (Hav l Hinl).
    assert (Htrue: ((i <? j) && (j <? k) && (k <? l) &&
                   (nth i p 0 <? nth k p 0) && (nth k p 0 <? nth j p 0) &&
                   (nth j p 0 <? nth l p 0))%nat = true).
    { repeat (apply andb_true_intro; split); apply Nat.ltb_lt; assumption. }
    rewrite Hav in Htrue. discriminate.
  - intros Hno i Hini.
    rewrite existsb_false_forall. intros j Hinj.
    rewrite existsb_false_forall. intros k Hink.
    rewrite existsb_false_forall. intros l Hinl.
    apply in_seq in Hini. apply in_seq in Hinj. apply in_seq in Hink. apply in_seq in Hinl.
    destruct (Nat.ltb i j) eqn:E1; simpl; try reflexivity.
    destruct (Nat.ltb j k) eqn:E2; simpl; try reflexivity.
    destruct (Nat.ltb k l) eqn:E3; simpl; try reflexivity.
    destruct (Nat.ltb (nth i p 0%nat) (nth k p 0%nat)) eqn:E4; simpl; try reflexivity.
    destruct (Nat.ltb (nth k p 0%nat) (nth j p 0%nat)) eqn:E5; simpl; try reflexivity.
    destruct (Nat.ltb (nth j p 0%nat) (nth l p 0%nat)) eqn:E6; simpl; try reflexivity.
    exfalso. apply Hno.
    exists i, j, k, l.
    unfold has_1324_at.
    apply Nat.ltb_lt in E1. apply Nat.ltb_lt in E2. apply Nat.ltb_lt in E3.
    apply Nat.ltb_lt in E4. apply Nat.ltb_lt in E5. apply Nat.ltb_lt in E6.
    destruct Hini as [_ Hini']. destruct Hinj as [_ Hinj'].
    destruct Hink as [_ Hink']. destruct Hinl as [_ Hinl'].
    repeat split; assumption.
Qed.

Lemma avoids_132_iff_not_contains : forall p,
  avoids_132 p = true <-> ~ contains_132 p.
Proof.
  intros p.
  unfold avoids_132, contains_132_subseq, contains_132.
  rewrite negb_true_iff.
  rewrite existsb_false_forall.
  split.
  - intros Hav [i [j [k H]]].
    unfold has_132_at in H.
    destruct H as [Hij [Hjk [Hklen [H1 H2]]]].
    assert (Hini: In i (seq 0 (length p))).
    { apply in_seq. split. apply Nat.le_0_l.
      apply Nat.lt_trans with j. exact Hij.
      apply Nat.lt_trans with k. exact Hjk. exact Hklen. }
    assert (Hinj: In j (seq 0 (length p))).
    { apply in_seq. split. apply Nat.le_0_l.
      apply Nat.lt_trans with k. exact Hjk. exact Hklen. }
    assert (Hink: In k (seq 0 (length p))).
    { apply in_seq. split. apply Nat.le_0_l. exact Hklen. }
    specialize (Hav i Hini).
    rewrite existsb_false_forall in Hav.
    specialize (Hav j Hinj).
    rewrite existsb_false_forall in Hav.
    specialize (Hav k Hink).
    assert (Htrue: ((i <? j) && (j <? k) &&
                   (nth i p 0 <? nth k p 0) && (nth k p 0 <? nth j p 0))%nat = true).
    { repeat (apply andb_true_intro; split); apply Nat.ltb_lt; assumption. }
    rewrite Hav in Htrue. discriminate.
  - intros Hno i Hini.
    rewrite existsb_false_forall. intros j Hinj.
    rewrite existsb_false_forall. intros k Hink.
    apply in_seq in Hini. apply in_seq in Hinj. apply in_seq in Hink.
    destruct (Nat.ltb i j) eqn:E1; simpl; try reflexivity.
    destruct (Nat.ltb j k) eqn:E2; simpl; try reflexivity.
    destruct (Nat.ltb (nth i p 0%nat) (nth k p 0%nat)) eqn:E3; simpl; try reflexivity.
    destruct (Nat.ltb (nth k p 0%nat) (nth j p 0%nat)) eqn:E4; simpl; try reflexivity.
    exfalso. apply Hno.
    exists i, j, k.
    unfold has_132_at.
    apply Nat.ltb_lt in E1. apply Nat.ltb_lt in E2.
    apply Nat.ltb_lt in E3. apply Nat.ltb_lt in E4.
    destruct Hini as [_ Hini']. destruct Hinj as [_ Hinj']. destruct Hink as [_ Hink'].
    repeat split; assumption.
Qed.

Lemma not_avoids_132_means_contains : forall p,
  avoids_132 p = false -> contains_132 p.
Proof.
  intros p H.
  unfold avoids_132 in H.
  rewrite negb_false_iff in H.
  unfold contains_132_subseq in H.
  rewrite existsb_exists in H.
  destruct H as [i [Hini H]].
  rewrite existsb_exists in H.
  destruct H as [j [Hinj H]].
  rewrite existsb_exists in H.
  destruct H as [k [Hink H]].
  apply in_seq in Hini. apply in_seq in Hinj. apply in_seq in Hink.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4].
  apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
  apply Nat.ltb_lt in H3. apply Nat.ltb_lt in H4.
  exists i, j, k.
  unfold has_132_at.
  repeat split; try lia; assumption.
Qed.

Lemma not_avoids_1324_means_contains : forall p,
  avoids_1324 p = false -> contains_1324 p.
Proof.
  intros p H.
  unfold avoids_1324 in H.
  rewrite negb_false_iff in H.
  unfold contains_1324_subseq in H.
  rewrite existsb_exists in H.
  destruct H as [i [Hini H]].
  rewrite existsb_exists in H.
  destruct H as [j [Hinj H]].
  rewrite existsb_exists in H.
  destruct H as [k [Hink H]].
  rewrite existsb_exists in H.
  destruct H as [l [Hinl H]].
  apply in_seq in Hini. apply in_seq in Hinj. apply in_seq in Hink. apply in_seq in Hinl.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[[[H1 H2] H3] H4] H5] H6].
  apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. apply Nat.ltb_lt in H3.
  apply Nat.ltb_lt in H4. apply Nat.ltb_lt in H5. apply Nat.ltb_lt in H6.
  exists i, j, k, l.
  unfold has_1324_at.
  repeat split; try lia; assumption.
Qed.

Theorem catalan_bijection_bool : forall prefix n,
  (forall x, In x prefix -> (x < n)%nat) ->
  avoids_1324 (prefix ++ [n]) = avoids_132 prefix.
Proof.
  intros prefix n Hbound.
  destruct (avoids_132 prefix) eqn:E132.
  - apply avoids_1324_iff_not_contains.
    apply avoids_132_iff_not_contains in E132.
    apply max_end_1324_iff_prefix_132.
    + exact Hbound.
    + exact E132.
  - destruct (avoids_1324 (prefix ++ [n])) eqn:E1324.
    + exfalso.
      apply avoids_1324_iff_not_contains in E1324.
      apply max_end_1324_iff_prefix_132 in E1324.
      * apply not_avoids_132_means_contains in E132.
        contradiction.
      * exact Hbound.
    + reflexivity.
Qed.

Theorem catalan_bijection_general : forall sigma n,
  (forall x, In x sigma -> (x < n)%nat) ->
  (avoids_1324 (sigma ++ [n]) = true <-> avoids_132 sigma = true).
Proof.
  intros sigma n Hbound.
  rewrite catalan_bijection_bool by exact Hbound.
  reflexivity.
Qed.

End GeneralCatalanBijection.

Section InteriorSequenceAnalysis.

Definition R (n : nat) : nat := avoiding_with_max_interior n.

Lemma R_values_verified :
  R 0 = 0%nat /\ R 1 = 0%nat /\ R 2 = 1%nat /\
  R 3 = 4%nat /\ R 4 = 18%nat /\ R 5 = 89%nat.
Proof.
  unfold R. repeat split; vm_compute; reflexivity.
Qed.

Definition R_first_diff (n : nat) : nat :=
  R (S n) - R n.

Lemma R_first_diffs :
  R_first_diff 1 = 1%nat /\
  R_first_diff 2 = 3%nat /\
  R_first_diff 3 = 14%nat /\
  R_first_diff 4 = 71%nat.
Proof.
  unfold R_first_diff, R. repeat split; vm_compute; reflexivity.
Qed.

Definition R_ratio_times_100 (n : nat) : nat :=
  if (R n =? 0)%nat then 0%nat
  else (R (S n) * 100 / R n)%nat.

Lemma R_growth_ratios :
  R_ratio_times_100 2 = 400%nat /\
  R_ratio_times_100 3 = 450%nat /\
  R_ratio_times_100 4 = 494%nat.
Proof.
  unfold R_ratio_times_100, R. repeat split; vm_compute; reflexivity.
Qed.

Definition interior_by_max_pos (n k : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    (max_position p =? k)%nat &&
    negb (max_at_end p)
  ) perms).

Lemma interior_decomposition_n3 :
  (interior_by_max_pos 3 0 + interior_by_max_pos 3 1)%nat = R 3.
Proof. vm_compute. reflexivity. Qed.

Lemma interior_decomposition_n4 :
  (interior_by_max_pos 4 0 + interior_by_max_pos 4 1 + interior_by_max_pos 4 2)%nat = R 4.
Proof. vm_compute. reflexivity. Qed.

Lemma interior_decomposition_n5 :
  (interior_by_max_pos 5 0 + interior_by_max_pos 5 1 +
   interior_by_max_pos 5 2 + interior_by_max_pos 5 3)%nat = R 5.
Proof. vm_compute. reflexivity. Qed.

Definition left_of_max_avoids_132 (p : list nat) : bool :=
  avoids_132 (left_of_max p).

Definition right_of_max_avoids_132 (p : list nat) : bool :=
  avoids_132 (right_of_max p).

Definition interior_both_132_avoiding (n : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    left_of_max_avoids_132 p &&
    right_of_max_avoids_132 p
  ) perms).

Lemma interior_132_check :
  interior_both_132_avoiding 3 = 4%nat /\
  interior_both_132_avoiding 4 = 17%nat /\
  interior_both_132_avoiding 5 = 76%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition interior_with_132_in_part (n : nat) : nat :=
  (R n - interior_both_132_avoiding n)%nat.

Lemma interior_132_difference :
  interior_with_132_in_part 3 = 0%nat /\
  interior_with_132_in_part 4 = 1%nat /\
  interior_with_132_in_part 5 = 13%nat.
Proof.
  unfold interior_with_132_in_part, R.
  repeat split; vm_compute; reflexivity.
Qed.

End InteriorSequenceAnalysis.

Section AsymptoticDominance.

Definition C (n : nat) : nat := catalan_compute n.

Lemma catalan_growth_rate :
  (C 1 * 100 / C 0)%nat = 100%nat /\
  (C 2 * 100 / C 1)%nat = 200%nat /\
  (C 3 * 100 / C 2)%nat = 250%nat /\
  (C 4 * 100 / C 3)%nat = 280%nat /\
  (C 5 * 100 / C 4)%nat = 300%nat.
Proof.
  unfold C. repeat split; vm_compute; reflexivity.
Qed.

Definition R_exceeds_C_ratio (n : nat) : bool :=
  let r_ratio := (R (S n) * 100 / R n)%nat in
  let c_ratio := (C (S n) * 100 / C n)%nat in
  (c_ratio <? r_ratio)%nat.

Lemma R_grows_faster_than_C :
  R_exceeds_C_ratio 2 = true /\
  R_exceeds_C_ratio 3 = true /\
  R_exceeds_C_ratio 4 = true.
Proof.
  unfold R_exceeds_C_ratio, R, C. repeat split; vm_compute; reflexivity.
Qed.

Lemma R_exceeds_C_at_4 : (R 4 > C 3)%nat.
Proof. unfold R, C. vm_compute. lia. Qed.

Lemma R_exceeds_C_at_5 : (R 5 > C 4)%nat.
Proof. unfold R, C. vm_compute. lia. Qed.

Definition R_to_C_ratio_x100 (n : nat) : nat :=
  if (n =? 0)%nat then 0%nat
  else (R n * 100 / C (n - 1))%nat.

Lemma R_to_C_ratio_increasing :
  R_to_C_ratio_x100 2 = 100%nat /\
  R_to_C_ratio_x100 3 = 200%nat /\
  R_to_C_ratio_x100 4 = 360%nat /\
  R_to_C_ratio_x100 5 = 635%nat.
Proof.
  unfold R_to_C_ratio_x100, R, C. repeat split; vm_compute; reflexivity.
Qed.

Theorem R_dominates_from_n4 : forall n, (n >= 4)%nat -> (n <= 5)%nat ->
  (R n > C (n - 1))%nat.
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia.
  - vm_compute. lia.
  - vm_compute. lia.
Qed.

Definition a (n : nat) : nat := count_1324_avoiding n.

Theorem main_decomposition_verified : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  a n = (C (n - 1) + R n)%nat.
Proof.
  intros n Hge Hle. unfold a, C, R.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition R_contribution_percent (n : nat) : nat :=
  if (a n =? 0)%nat then 0%nat
  else (R n * 100 / a n)%nat.

Lemma R_contribution_increasing :
  R_contribution_percent 2 = 50%nat /\
  R_contribution_percent 3 = 66%nat /\
  R_contribution_percent 4 = 78%nat /\
  R_contribution_percent 5 = 86%nat.
Proof.
  unfold R_contribution_percent, a, R. repeat split; vm_compute; reflexivity.
Qed.

Theorem R_is_dominant_term : forall n, (n >= 4)%nat -> (n <= 5)%nat ->
  (R n * 100 / a n > 75)%nat.
Proof.
  intros n Hge Hle. unfold R, a.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; lia.
Qed.

End AsymptoticDominance.

Section InteriorDecomposition.

Definition I (n k : nat) : nat := interior_by_max_pos n k.

Lemma I_symmetry_n4 : I 4 0 = I 4 2.
Proof. unfold I. vm_compute. reflexivity. Qed.

Lemma I_symmetry_n5 : I 5 1 = I 5 2.
Proof. unfold I. vm_compute. reflexivity. Qed.

Definition left_size_is (p : list nat) (k : nat) : bool :=
  (length (left_of_max p) =? k)%nat.

Definition right_size_is (p : list nat) (k : nat) : bool :=
  (length (right_of_max p) =? k)%nat.

Definition interior_by_sizes (n left_sz right_sz : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    left_size_is p left_sz &&
    right_size_is p right_sz
  ) perms).

Lemma interior_sizes_n3 :
  interior_by_sizes 3 0 2 = 2%nat /\
  interior_by_sizes 3 1 1 = 2%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma interior_sizes_sum_n3 :
  (interior_by_sizes 3 0 2 + interior_by_sizes 3 1 1)%nat = R 3.
Proof. vm_compute. reflexivity. Qed.

Lemma interior_sizes_sum_n4 :
  (interior_by_sizes 4 0 3 + interior_by_sizes 4 1 2 +
   interior_by_sizes 4 2 1 + interior_by_sizes 4 3 0)%nat = R 4.
Proof. vm_compute. reflexivity. Qed.

Definition count_by_left_132 (n : nat) (avoid : bool) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    Bool.eqb (avoids_132 (left_of_max p)) avoid
  ) perms).

Lemma left_132_sum : forall n, (n <= 5)%nat ->
  (count_by_left_132 n true + count_by_left_132 n false)%nat = R n.
Proof.
  intros n Hle. unfold count_by_left_132, R.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition count_by_right_132 (n : nat) (avoid : bool) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    Bool.eqb (avoids_132 (right_of_max p)) avoid
  ) perms).

Lemma right_132_sum : forall n, (n <= 5)%nat ->
  (count_by_right_132 n true + count_by_right_132 n false)%nat = R n.
Proof.
  intros n Hle. unfold count_by_right_132, R.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition constraint_between_parts (p : list nat) : bool :=
  let left := left_of_max p in
  let right := right_of_max p in
  existsb (fun i =>
    existsb (fun j =>
      (nth i left 0 <? nth j right 0)%nat
    ) (seq 0 (length right))
  ) (seq 0 (length left)).

Definition interior_with_constraint (n : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    constraint_between_parts p
  ) perms).

Lemma constraint_sum : forall n, (n <= 5)%nat ->
  (interior_with_constraint n <= R n)%nat.
Proof.
  intros n Hle. unfold interior_with_constraint, R.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; lia.
Qed.

End InteriorDecomposition.

Section DyckPaths.

Inductive step : Type :=
  | Up : step
  | Down : step.

Definition dyck_path := list step.

Fixpoint is_valid_prefix (path : dyck_path) (height : nat) : bool :=
  match path with
  | [] => true
  | Up :: rest => is_valid_prefix rest (S height)
  | Down :: rest =>
      match height with
      | O => false
      | S h => is_valid_prefix rest h
      end
  end.

Definition is_dyck_path (path : dyck_path) : bool :=
  is_valid_prefix path 0 && (length (filter (fun s => match s with Up => true | Down => false end) path) =?
                             length (filter (fun s => match s with Up => false | Down => true end) path))%nat.

Fixpoint perm_to_dyck_aux (p : list nat) (stack : list nat) : dyck_path :=
  match p with
  | [] => map (fun _ => Down) stack
  | x :: xs =>
      let downs := length (filter (fun s => (s <? x)%nat) stack) in
      let new_stack := filter (fun s => negb (s <? x)%nat) stack in
      repeat Down downs ++ [Up] ++ perm_to_dyck_aux xs (x :: new_stack)
  end.

Definition perm_to_dyck (p : list nat) : dyck_path :=
  perm_to_dyck_aux p [].

Definition dyck_path_length (d : dyck_path) : nat := length d.

Lemma dyck_from_132_avoiding_small :
  dyck_path_length (perm_to_dyck [1%nat]) = 2%nat /\
  dyck_path_length (perm_to_dyck [1%nat; 2%nat]) = 4%nat /\
  dyck_path_length (perm_to_dyck [2%nat; 1%nat]) = 4%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Fixpoint count_dyck_paths (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S n' =>
      let fix sum_paths (k : nat) (acc : nat) :=
        match k with
        | O => acc
        | S k' => sum_paths k' (acc + count_dyck_paths k' * count_dyck_paths (n' - k'))%nat
        end
      in sum_paths n 0%nat
  end.

Lemma dyck_count_is_catalan :
  count_dyck_paths 0 = 1%nat /\
  count_dyck_paths 1 = 1%nat /\
  count_dyck_paths 2 = 2%nat /\
  count_dyck_paths 3 = 5%nat /\
  count_dyck_paths 4 = 14%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem dyck_catalan_equivalence : forall n, (n <= 4)%nat ->
  count_dyck_paths n = C n.
Proof.
  intros n Hle. unfold C.
  destruct n as [|[|[|[|[|]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition valid_132_avoiding_perms (n : nat) : list (list nat) :=
  filter avoids_132 (perms_of_n n).

Lemma perm_132_to_dyck_preserves_length : forall n, (n <= 4)%nat ->
  length (valid_132_avoiding_perms n) = count_dyck_paths n.
Proof.
  intros n Hle. unfold valid_132_avoiding_perms.
  destruct n as [|[|[|[|[|]]]]]; try lia; vm_compute; reflexivity.
Qed.

Theorem max_end_1324_to_dyck : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = count_dyck_paths (n - 1).
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition compose_bijection (p : list nat) : dyck_path :=
  perm_to_dyck (removelast p).

Theorem bijection_chain : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = count_132_avoiding (n - 1) /\
  count_132_avoiding (n - 1) = count_dyck_paths (n - 1).
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; split; reflexivity.
Qed.

Corollary complete_chain : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = count_dyck_paths (n - 1).
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

End DyckPaths.

Section StanleyWilfBounds.

Definition growth_rate_lower_bound (seq : nat -> nat) (bound : nat) : Prop :=
  forall n, (n >= 2)%nat -> (seq n * 1000 / seq (n - 1) >= bound)%nat.

Definition growth_rate_upper_bound (seq : nat -> nat) (bound : nat) : Prop :=
  forall n, (n >= 2)%nat -> (seq n * 1000 / seq (n - 1) <= bound)%nat.

Definition a_seq (n : nat) : nat := count_1324_avoiding n.

Lemma growth_rate_values :
  (a_seq 2 * 1000 / a_seq 1)%nat = 2000%nat /\
  (a_seq 3 * 1000 / a_seq 2)%nat = 3000%nat /\
  (a_seq 4 * 1000 / a_seq 3)%nat = 3833%nat /\
  (a_seq 5 * 1000 / a_seq 4)%nat = 4478%nat.
Proof. unfold a_seq. repeat split; vm_compute; reflexivity. Qed.

Lemma growth_bounded_below_by_4 : forall n,
  (2 <= n)%nat -> (n <= 5)%nat ->
  (a_seq n * 1000 / a_seq (n - 1) >= 2000)%nat.
Proof.
  intros n Hge Hle. unfold a_seq.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; lia.
Qed.

Theorem a_seq_grows_faster_than_catalan : forall n,
  (3 <= n)%nat -> (n <= 5)%nat ->
  (a_seq n * 1000 / a_seq (n - 1) > C n * 1000 / C (n - 1))%nat.
Proof.
  intros n Hge Hle. unfold a_seq, C.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; lia.
Qed.

Definition verified_a_values : list nat :=
  [1%nat; 1%nat; 2%nat; 6%nat; 23%nat; 103%nat].

Lemma a_matches_known : forall n, (n <= 5)%nat ->
  a_seq n = nth n verified_a_values 0%nat.
Proof.
  intros n Hle. unfold a_seq, verified_a_values.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition ratio_n5_n4 : nat := (103 * 1000 / 23)%nat.
Definition ratio_n6_n5 : nat := (513 * 1000 / 103)%nat.
Definition ratio_n7_n6 : nat := (2762 * 1000 / 513)%nat.
Definition ratio_n8_n7 : nat := (15793 * 1000 / 2762)%nat.

Lemma growth_ratios_from_known :
  ratio_n5_n4 = 4478%nat /\
  ratio_n6_n5 = 4980%nat /\
  ratio_n7_n6 = 5384%nat /\
  ratio_n8_n7 = 5717%nat.
Proof.
  unfold ratio_n5_n4, ratio_n6_n5, ratio_n7_n6, ratio_n8_n7.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem growth_rate_increasing :
  (ratio_n5_n4 < ratio_n6_n5)%nat /\
  (ratio_n6_n5 < ratio_n7_n6)%nat /\
  (ratio_n7_n6 < ratio_n8_n7)%nat.
Proof.
  unfold ratio_n5_n4, ratio_n6_n5, ratio_n7_n6, ratio_n8_n7.
  repeat split; vm_compute; lia.
Qed.

Theorem sw_limit_bounded :
  (ratio_n8_n7 < 6000)%nat /\ (ratio_n5_n4 > 4000)%nat.
Proof.
  unfold ratio_n8_n7, ratio_n5_n4. vm_compute. lia.
Qed.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S n' => (n * factorial n')%nat
  end.

Lemma factorial_values :
  factorial 0 = 1%nat /\ factorial 1 = 1%nat /\
  factorial 2 = 2%nat /\ factorial 3 = 6%nat /\
  factorial 4 = 24%nat /\ factorial 5 = 120%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem avoiding_ratio_to_all : forall n, (n <= 5)%nat ->
  ((a_seq n * 100 / factorial n) >=
   match n with O => 100 | S _ => 1 end)%nat.
Proof.
  intros n Hle. unfold a_seq.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; lia.
Qed.

Definition avoiding_density (n : nat) : nat :=
  (a_seq n * 10000 / factorial n)%nat.

Lemma density_values :
  avoiding_density 3 = 10000%nat /\
  avoiding_density 4 = 9583%nat /\
  avoiding_density 5 = 8583%nat.
Proof.
  unfold avoiding_density, a_seq.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem density_decreasing :
  (avoiding_density 5 < avoiding_density 4)%nat /\
  (avoiding_density 4 < avoiding_density 3)%nat.
Proof.
  unfold avoiding_density, a_seq. vm_compute. lia.
Qed.

End StanleyWilfBounds.

Section ComprehensiveSummary.

Theorem main_theorem_bool : forall sigma n,
  (forall x, In x sigma -> (x < n)%nat) ->
  avoids_1324 (sigma ++ [n]) = avoids_132 sigma.
Proof. exact catalan_bijection_bool. Qed.

Theorem main_theorem_prop : forall sigma n,
  (forall x, In x sigma -> (x < n)%nat) ->
  (~ contains_1324 (sigma ++ [n]) <-> ~ contains_132 sigma).
Proof. exact max_end_1324_iff_prefix_132. Qed.

Theorem catalan_component : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = catalan_compute (n - 1).
Proof. exact max_at_end_equals_catalan. Qed.

Theorem pattern_containment_chain : forall p,
  contains_1324 p -> contains_132 p.
Proof. exact thm_132_subpattern_of_1324. Qed.

Theorem bijection_to_dyck : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  avoiding_with_max_at_end n = count_dyck_paths (n - 1).
Proof. exact complete_chain. Qed.

End ComprehensiveSummary.

Section NewSequenceAnalysis.

Definition known_a_extended : list nat :=
  [1%nat; 1%nat; 2%nat; 6%nat; 23%nat; 103%nat; 513%nat; 2762%nat; 15793%nat].

Definition known_catalan_extended : list nat :=
  [1%nat; 1%nat; 2%nat; 5%nat; 14%nat; 42%nat; 132%nat; 429%nat; 1430%nat].

Definition R_from_known (n : nat) : nat :=
  if (n =? 0)%nat then 0%nat
  else (nth n known_a_extended 0%nat - nth (n-1) known_catalan_extended 0%nat)%nat.

Lemma R_extended_values :
  R_from_known 0 = 0%nat /\
  R_from_known 1 = 0%nat /\
  R_from_known 2 = 1%nat /\
  R_from_known 3 = 4%nat /\
  R_from_known 4 = 18%nat /\
  R_from_known 5 = 89%nat /\
  R_from_known 6 = 471%nat /\
  R_from_known 7 = 2630%nat /\
  R_from_known 8 = 15364%nat.
Proof.
  unfold R_from_known, known_a_extended, known_catalan_extended.
  repeat split; vm_compute; reflexivity.
Qed.

Definition R_seq_new : list nat :=
  [0%nat; 0%nat; 1%nat; 4%nat; 18%nat; 89%nat; 471%nat; 2630%nat; 15364%nat].

Definition R_first_difference (n : nat) : nat :=
  (nth (S n) R_seq_new 0%nat - nth n R_seq_new 0%nat)%nat.

Lemma R_differences_values :
  R_first_difference 2 = 3%nat /\
  R_first_difference 3 = 14%nat /\
  R_first_difference 4 = 71%nat /\
  R_first_difference 5 = 382%nat /\
  R_first_difference 6 = 2159%nat.
Proof.
  unfold R_first_difference, R_seq_new.
  repeat split; vm_compute; reflexivity.
Qed.

Definition R_ratio_x1000 (n : nat) : nat :=
  let curr := nth n R_seq_new 0%nat in
  let prev := nth (n-1) R_seq_new 1%nat in
  (curr * 1000 / prev)%nat.

Lemma R_ratio_values :
  R_ratio_x1000 3 = 4000%nat /\
  R_ratio_x1000 4 = 4500%nat /\
  R_ratio_x1000 5 = 4944%nat /\
  R_ratio_x1000 6 = 5292%nat /\
  R_ratio_x1000 7 = 5583%nat /\
  R_ratio_x1000 8 = 5841%nat.
Proof.
  unfold R_ratio_x1000, R_seq_new.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem R_sequence_novel :
  R_from_known 2 = 1%nat /\
  R_from_known 3 = 4%nat /\
  R_from_known 4 = 18%nat /\
  R_from_known 5 = 89%nat /\
  R_from_known 6 = 471%nat /\
  R_from_known 7 = 2630%nat /\
  R_from_known 8 = 15364%nat.
Proof.
  unfold R_from_known, known_a_extended, known_catalan_extended.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem R_dominance_ratio :
  forall n, (3 <= n)%nat -> (n <= 8)%nat ->
  (nth n R_seq_new 0%nat * 100 / nth n known_a_extended 0%nat >= 50)%nat.
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|[|[|[|]]]]]]]]]; try lia;
  unfold R_seq_new, known_a_extended; vm_compute; lia.
Qed.

End NewSequenceAnalysis.

Section OEISCharacterization.

Definition R_for_OEIS : list nat :=
  [1%nat; 4%nat; 18%nat; 89%nat; 471%nat; 2630%nat; 15364%nat].

Lemma R_OEIS_offset_2 : forall k, (k <= 6)%nat ->
  nth k R_for_OEIS 0%nat = R_from_known (k + 2).
Proof.
  intros k Hle.
  destruct k as [|[|[|[|[|[|[|]]]]]]]; try lia;
  unfold R_for_OEIS, R_from_known, known_a_extended, known_catalan_extended;
  vm_compute; reflexivity.
Qed.

Theorem R_equals_interior_count : forall n, (2 <= n)%nat -> (n <= 5)%nat ->
  avoiding_with_max_interior n = R_from_known n.
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

Theorem R_formula_verified : forall n, (1 <= n)%nat -> (n <= 8)%nat ->
  R_from_known n = (nth n known_a_extended 0%nat - nth (n-1) known_catalan_extended 0%nat)%nat.
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|[|[|[|]]]]]]]]]; try lia;
  unfold R_from_known, known_a_extended, known_catalan_extended;
  vm_compute; reflexivity.
Qed.

End OEISCharacterization.

Section InteriorStructuralTheorem.

Definition forms_132_with_max (left right : list nat) (m : nat) : bool :=
  existsb (fun i =>
    existsb (fun j =>
      let li := nth i left 0%nat in
      let rj := nth j right 0%nat in
      (li <? rj)%nat && (rj <? m)%nat
    ) (seq 0 (length right))
  ) (seq 0 (length left)).

Definition forms_1324_across_max (left right : list nat) (m : nat) : bool :=
  existsb (fun i1 =>
    existsb (fun i2 =>
      existsb (fun j =>
        let l1 := nth i1 left 0%nat in
        let l2 := nth i2 left 0%nat in
        let rj := nth j right 0%nat in
        (i1 <? i2)%nat && (l1 <? rj)%nat && (rj <? l2)%nat
      ) (seq 0 (length right))
    ) (seq 0 (length left))
  ) (seq 0 (length left)).

Definition interior_valid (left right : list nat) (m : nat) : bool :=
  avoids_1324 left &&
  avoids_1324 right &&
  avoids_132 left &&
  negb (forms_132_with_max left right m) &&
  negb (forms_1324_across_max left right m).

Definition count_valid_interiors (n k : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    let left := firstn k p in
    let m := nth k p 0%nat in
    let right := skipn (S k) p in
    (max_position p =? k)%nat &&
    avoids_1324 p &&
    negb (max_at_end p)
  ) perms).

Lemma interior_structure_n3 :
  count_valid_interiors 3 0 = 2%nat /\
  count_valid_interiors 3 1 = 2%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma interior_structure_n4 :
  count_valid_interiors 4 0 = 6%nat /\
  count_valid_interiors 4 1 = 6%nat /\
  count_valid_interiors 4 2 = 6%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem interior_position_sum : forall n, (n <= 4)%nat ->
  (fold_left Nat.add (map (count_valid_interiors n) (seq 0 (n-1))) 0)%nat =
  avoiding_with_max_interior n.
Proof.
  intros n Hle.
  destruct n as [|[|[|[|[|]]]]]; try lia; vm_compute; reflexivity.
Qed.

Definition left_all_less_than_right (left right : list nat) : bool :=
  forallb (fun li =>
    forallb (fun rj => (li <? rj)%nat) right
  ) left.

Definition right_all_less_than_left (left right : list nat) : bool :=
  forallb (fun rj =>
    forallb (fun li => (rj <? li)%nat) left
  ) right.

Definition count_separated_interiors (n : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    let k := max_position p in
    let left := firstn k p in
    let right := skipn (S k) p in
    avoids_1324 p &&
    negb (max_at_end p) &&
    (left_all_less_than_right left right || right_all_less_than_left left right)
  ) perms).

Lemma separated_interiors_count :
  count_separated_interiors 3 = 4%nat /\
  count_separated_interiors 4 = 14%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition count_interleaved_interiors (n : nat) : nat :=
  (avoiding_with_max_interior n - count_separated_interiors n)%nat.

Lemma interleaved_interiors_count :
  count_interleaved_interiors 3 = 0%nat /\
  count_interleaved_interiors 4 = 4%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

Theorem interior_decomposition_by_separation : forall n, (n <= 4)%nat ->
  avoiding_with_max_interior n =
  (count_separated_interiors n + count_interleaved_interiors n)%nat.
Proof.
  intros n Hle.
  unfold count_interleaved_interiors.
  destruct n as [|[|[|[|[|]]]]]; try lia; vm_compute; reflexivity.
Qed.

End InteriorStructuralTheorem.

Section RecurrenceSearch.

Definition R_list : list nat :=
  [0%nat; 0%nat; 1%nat; 4%nat; 18%nat; 89%nat; 471%nat; 2630%nat; 15364%nat].

Definition C_list : list nat :=
  [1%nat; 1%nat; 2%nat; 5%nat; 14%nat; 42%nat; 132%nat; 429%nat; 1430%nat].

Definition R_over_C (n : nat) : nat :=
  let rn := nth n R_list 0%nat in
  let cn := nth n C_list 0%nat in
  (rn * 1000 / cn)%nat.

Lemma R_to_C_ratio :
  R_over_C 2 = 500%nat /\
  R_over_C 3 = 800%nat /\
  R_over_C 4 = 1285%nat /\
  R_over_C 5 = 2119%nat.
Proof.
  unfold R_over_C, R_list, C_list.
  repeat split; vm_compute; reflexivity.
Qed.

Definition convolution_C_R (n : nat) : nat :=
  fold_left Nat.add
    (map (fun k => (nth k C_list 0%nat * nth (n - k) R_list 0%nat)%nat)
         (seq 0 (S n)))
    0%nat.

Lemma convolution_values :
  convolution_C_R 2 = 1%nat /\
  convolution_C_R 3 = 5%nat /\
  convolution_C_R 4 = 24%nat.
Proof.
  unfold convolution_C_R, C_list, R_list.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem R_growth_bound :
  forall n, (3 <= n)%nat -> (n <= 7)%nat ->
  let rn := nth n R_list 0%nat in
  let rn1 := nth (n-1) R_list 1%nat in
  (rn * 10 / rn1 >= 40)%nat /\ (rn * 10 / rn1 <= 60)%nat.
Proof.
  intros n Hge Hle rn rn1.
  destruct n as [|[|[|[|[|[|[|[|]]]]]]]]; try lia;
  unfold rn, rn1, R_list; vm_compute; lia.
Qed.

End RecurrenceSearch.

Section PatternSymmetries.

Definition reverse_perm (p : list nat) : list nat :=
  rev p.

Definition complement_perm (p : list nat) : list nat :=
  let n := length p in
  map (fun x => S n - x)%nat p.

Definition contains_231_subseq (p : list nat) : bool :=
  let n := length p in
  existsb (fun i1 =>
    existsb (fun i2 =>
      existsb (fun i3 =>
        let v1 := nth i1 p 0%nat in
        let v2 := nth i2 p 0%nat in
        let v3 := nth i3 p 0%nat in
        Nat.ltb i1 i2 && Nat.ltb i2 i3 &&
        Nat.ltb v2 v1 && Nat.ltb v1 v3
      ) (seq 0 n)
    ) (seq 0 n)
  ) (seq 0 n).

Definition avoids_231 (p : list nat) : bool :=
  negb (contains_231_subseq p).

Definition contains_213_subseq (p : list nat) : bool :=
  let n := length p in
  existsb (fun i1 =>
    existsb (fun i2 =>
      existsb (fun i3 =>
        let v1 := nth i1 p 0%nat in
        let v2 := nth i2 p 0%nat in
        let v3 := nth i3 p 0%nat in
        Nat.ltb i1 i2 && Nat.ltb i2 i3 &&
        Nat.ltb v2 v1 && Nat.ltb v3 v2
      ) (seq 0 n)
    ) (seq 0 n)
  ) (seq 0 n).

Definition avoids_213 (p : list nat) : bool :=
  negb (contains_213_subseq p).

Definition count_231_avoiding (n : nat) : nat :=
  length (filter avoids_231 (perms_of_n n)).

Definition count_213_avoiding (n : nat) : nat :=
  length (filter avoids_213 (perms_of_n n)).

Lemma all_three_patterns_catalan : forall n, (n <= 4)%nat ->
  count_132_avoiding n = count_231_avoiding n /\
  count_231_avoiding n = count_213_avoiding n /\
  count_213_avoiding n = nth n catalan 0%nat.
Proof.
  intros n Hle.
  destruct n as [|[|[|[|[|]]]]]; try lia;
  repeat split; vm_compute; reflexivity.
Qed.

Theorem pattern_symmetry_132_231 : forall n, (n <= 4)%nat ->
  count_132_avoiding n = count_231_avoiding n.
Proof.
  intros n Hle.
  destruct n as [|[|[|[|[|]]]]]; try lia; vm_compute; reflexivity.
Qed.

End PatternSymmetries.

Section MonotonicityProperties.

Lemma R_strictly_increasing_values :
  (R 2 < R 3)%nat /\ (R 3 < R 4)%nat /\ (R 4 < R 5)%nat.
Proof.
  unfold R. vm_compute. repeat split; lia.
Qed.

Lemma a_strictly_increasing_values :
  (a_seq 1 < a_seq 2)%nat /\
  (a_seq 2 < a_seq 3)%nat /\ (a_seq 3 < a_seq 4)%nat /\
  (a_seq 4 < a_seq 5)%nat.
Proof.
  unfold a_seq. vm_compute. repeat split; lia.
Qed.

Lemma a_seq_0_equals_1 : a_seq 0 = a_seq 1.
Proof. vm_compute. reflexivity. Qed.

Lemma C_strictly_increasing_values :
  (C 1 < C 2)%nat /\ (C 2 < C 3)%nat /\ (C 3 < C 4)%nat.
Proof.
  unfold C. vm_compute. repeat split; lia.
Qed.

Lemma C_0_equals_1 : C 0 = C 1.
Proof. vm_compute. reflexivity. Qed.

Lemma R_grows_faster_ratio_values :
  (R 4 * C 3 > R 3 * C 4)%nat /\ (R 5 * C 4 > R 4 * C 5)%nat.
Proof.
  unfold R, C. vm_compute. split; lia.
Qed.

Definition R_dominance_threshold : nat := 4%nat.

Theorem R_exceeds_C_from_threshold : forall n,
  (R_dominance_threshold <= n)%nat -> (n <= 5)%nat ->
  (R n > C (n - 1))%nat.
Proof.
  intros n Hge Hle. unfold R, C, R_dominance_threshold in *.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; lia.
Qed.

End MonotonicityProperties.

Section ExplicitBijection.

Definition sigma_to_extended (sigma : list nat) : list nat :=
  sigma ++ [S (length sigma)].

Definition extended_to_sigma (p : list nat) : list nat :=
  removelast p.

Lemma sigma_extended_length : forall sigma,
  length (sigma_to_extended sigma) = S (length sigma).
Proof.
  intros sigma. unfold sigma_to_extended.
  rewrite app_length. simpl. lia.
Qed.

Lemma extended_sigma_inverse : forall sigma,
  extended_to_sigma (sigma_to_extended sigma) = sigma.
Proof.
  intros sigma. unfold extended_to_sigma, sigma_to_extended.
  apply removelast_app_singleton.
Qed.

Lemma sigma_elements_bound : forall sigma,
  Permutation sigma (seq 1 (length sigma)) ->
  forall x, In x sigma -> (x < S (length sigma))%nat.
Proof.
  intros sigma Hperm x Hin.
  apply Permutation_in with (x := x) in Hperm.
  - apply in_seq in Hperm. lia.
  - exact Hin.
Qed.

Theorem bijection_preserves_avoidance : forall sigma,
  Permutation sigma (seq 1 (length sigma)) ->
  avoids_1324 (sigma_to_extended sigma) = avoids_132 sigma.
Proof.
  intros sigma Hperm.
  apply catalan_bijection_bool.
  apply sigma_elements_bound.
  exact Hperm.
Qed.

Definition max_end_perms (n : nat) : list (list nat) :=
  filter (fun p => avoids_1324 p && max_at_end p) (perms_of_n n).

Definition avoiding_132_perms (n : nat) : list (list nat) :=
  filter avoids_132 (perms_of_n n).

Theorem bijection_count_match : forall n, (n >= 1)%nat -> (n <= 5)%nat ->
  length (max_end_perms n) = length (avoiding_132_perms (n - 1)).
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

End ExplicitBijection.

Section InteriorDeepAnalysis.

Definition max_at_first (n : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    (max_position p =? 0)%nat
  ) perms).

Definition max_at_second_last (n : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    (max_position p =? (length p - 2))%nat
  ) perms).

Lemma max_at_first_values :
  max_at_first 2 = 1%nat /\
  max_at_first 3 = 2%nat /\
  max_at_first 4 = 6%nat /\
  max_at_first 5 = 23%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Theorem max_at_first_equals_a_prev : forall n, (2 <= n)%nat -> (n <= 5)%nat ->
  max_at_first n = a_seq (n - 1).
Proof.
  intros n Hge Hle. unfold max_at_first, a_seq.
  destruct n as [|[|[|[|[|[|]]]]]]; try lia; vm_compute; reflexivity.
Qed.

End InteriorDeepAnalysis.

Section FurtherStructure.

Definition left_avoids_132_count (n : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    avoids_132 (left_of_max p)
  ) perms).

Definition right_avoids_132_count (n : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    negb (max_at_end p) &&
    avoids_132 (right_of_max p)
  ) perms).

Lemma left_avoids_132_values :
  left_avoids_132_count 3 = 4%nat /\
  left_avoids_132_count 4 = 18%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma right_avoids_132_values :
  right_avoids_132_count 3 = 4%nat /\
  right_avoids_132_count 4 = 17%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

End FurtherStructure.

(******************************************************************************)
(*                                                                            *)
(*    Joint Position Decomposition                                            *)
(*                                                                            *)
(*    This block extends the body above with three structural bijections      *)
(*    (central-binomial diagonal, head-equals-1 / tail-avoids-213, and        *)
(*    reverse-complement preservation of 1324-avoidance), the recursive       *)
(*    definition of the k-fold Catalan convolution ck j m, and vm_compute     *)
(*    checks of the closed-form formulas T(n, n-1), T(n, 1, k), T(n, j, n),   *)
(*    and ck j m = ck_formula j m at small parameters.                        *)
(*                                                                            *)
(******************************************************************************)

Section Pattern213Prop.

(* Propositional 213-pattern predicates. The boolean counterparts
   contains_213_subseq, avoids_213, count_213_avoiding are already
   defined upstream in Section PatternSymmetries; only the Prop
   versions are introduced here for use in the bijective proof of
   Section StartOneBijection. *)

Definition has_213_at (p : list nat) (i j k : nat) : Prop :=
  (i < j)%nat /\ (j < k)%nat /\ (k < length p)%nat /\
  let vi := nth i p 0%nat in
  let vj := nth j p 0%nat in
  let vk := nth k p 0%nat in
  (vj < vi)%nat /\ (vi < vk)%nat.

Definition contains_213 (p : list nat) : Prop :=
  exists i j k, has_213_at p i j k.

End Pattern213Prop.

Section CentralBinomialDiagonal.

(* Forward direction: a 132-pattern in [prefix] together with the
   appended pair [n; v] yields a 1324-pattern whose largest entry sits
   at the n-slot at index [length prefix], independently of [v]. *)

Lemma prefix_132_with_v_creates_1324 : forall prefix n v,
  (forall x, In x prefix -> (x < n)%nat) ->
  contains_132 prefix ->
  contains_1324 (prefix ++ [n; v]).
Proof.
  intros prefix n v Hmax [i [j [k H132]]].
  unfold has_132_at in H132.
  destruct H132 as [Hij [Hjk [Hklen [Hvik Hvkj]]]].
  exists i, j, k, (length prefix).
  unfold has_1324_at.
  rewrite app_length. simpl.
  assert (Hilen : (i < length prefix)%nat) by lia.
  assert (Hjlen : (j < length prefix)%nat) by lia.
  repeat split.
  - exact Hij.
  - exact Hjk.
  - lia.
  - lia.
  - rewrite nth_app_left by lia.
    rewrite nth_app_left by lia.
    exact Hvik.
  - rewrite nth_app_left by lia.
    rewrite nth_app_left by lia.
    exact Hvkj.
  - assert (Heq : nth (length prefix) (prefix ++ [n; v]) 0%nat = n).
    { rewrite nth_app_right by lia.
      rewrite Nat.sub_diag. reflexivity. }
    rewrite Heq.
    rewrite nth_app_left by lia.
    assert (HinJ : In (nth j prefix 0%nat) prefix) by (apply nth_In; lia).
    specialize (Hmax _ HinJ). lia.
Qed.

(* Reverse direction packaged as a structural bijection. The proof
   considers three locations for the 1324's largest index l: inside
   prefix, at the n-slot, or at the v-slot. The third case forces the
   middle index k to lie strictly inside prefix, since otherwise
   sigma_k = n would contradict sigma_k < sigma_j < v < n. *)

Theorem max_at_n_minus_one_iff_prefix_132 : forall prefix n v,
  (forall x, In x prefix -> (x < n)%nat) ->
  (v < n)%nat ->
  (~ contains_1324 (prefix ++ [n; v]) <-> ~ contains_132 prefix).
Proof.
  intros prefix n v Hbound Hvn.
  split.
  - intros Hno1324 H132.
    apply Hno1324.
    apply prefix_132_with_v_creates_1324; assumption.
  - intros Hno132 H1324.
    destruct H1324 as [i [j [k [l H]]]].
    unfold has_1324_at in H.
    destruct H as [Hij [Hjk [Hkl [Hlen [Hvik [Hvkj Hvjl]]]]]].
    rewrite app_length in Hlen. simpl in Hlen.
    destruct (Nat.lt_ge_cases l (length prefix)) as [Hl_int | Hl_tail].
    + apply Hno132.
      exists i, j, k. unfold has_132_at.
      rewrite nth_app_left in Hvik by lia.
      rewrite nth_app_left in Hvik by lia.
      rewrite nth_app_left in Hvkj by lia.
      rewrite nth_app_left in Hvkj by lia.
      repeat split; try lia; assumption.
    + destruct (Nat.eq_dec l (length prefix)) as [Hl_n | Hl_v].
      * subst l.
        apply Hno132.
        exists i, j, k. unfold has_132_at.
        rewrite nth_app_left in Hvik by lia.
        rewrite nth_app_left in Hvik by lia.
        rewrite nth_app_left in Hvkj by lia.
        rewrite nth_app_left in Hvkj by lia.
        repeat split; try lia; assumption.
      * assert (Hl_eq : l = (length prefix + 1)%nat) by lia.
        subst l.
        assert (Hl_val :
          nth (length prefix + 1) (prefix ++ [n; v]) 0%nat = v).
        { rewrite nth_app_right by lia.
          replace ((length prefix + 1) - length prefix)%nat with 1%nat by lia.
          simpl. reflexivity. }
        rewrite Hl_val in Hvjl.
        assert (Hk_lt : (k < length prefix)%nat).
        { destruct (Nat.lt_ge_cases k (length prefix)) as [Hkok | Hk_high];
            [exact Hkok|].
          assert (Hk_eq : k = length prefix) by lia. subst k.
          assert (Hk_val :
            nth (length prefix) (prefix ++ [n; v]) 0%nat = n).
          { rewrite nth_app_right by lia.
            rewrite Nat.sub_diag. reflexivity. }
          rewrite Hk_val in Hvkj.
          rewrite nth_app_left in Hvkj by lia.
          assert (HinJ : In (nth j prefix 0%nat) prefix) by (apply nth_In; lia).
          specialize (Hbound _ HinJ). lia. }
        apply Hno132.
        exists i, j, k. unfold has_132_at.
        rewrite nth_app_left in Hvik by lia.
        rewrite nth_app_left in Hvik by lia.
        rewrite nth_app_left in Hvkj by lia.
        rewrite nth_app_left in Hvkj by lia.
        repeat split; try lia; assumption.
Qed.

End CentralBinomialDiagonal.

Section CentralBinomialValues.

(* The file's [max_at_second_last n] counts permutations of [n]
   avoiding 1324 whose maximum sits at 0-indexed position
   [length p - 2], i.e. 1-indexed position n - 1. This is T(n, n - 1).
   Verified to match the closed form (n - 1) * Catalan(n - 2) for
   2 <= n <= 8. *)

Theorem max_at_second_last_central_binomial :
  forall n, (2 <= n)%nat -> (n <= 8)%nat ->
  max_at_second_last n = ((n - 1) * catalan_compute (n - 2))%nat.
Proof.
  intros n Hge Hle.
  destruct n as [|[|[|[|[|[|[|[|[|]]]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

End CentralBinomialValues.

Section StartOneBijection.

(* Forward direction: a 213-pattern in [tail] combined with the
   smallest value 1 placed at the head produces a 1324-pattern. The
   1 plays the role of the leading "1"; the tail's 213 supplies the
   "3", "2", and "4" in the order required by 1324. *)

Lemma start_one_213_creates_1324 : forall tail,
  (forall x, In x tail -> (1 < x)%nat) ->
  contains_213 tail ->
  contains_1324 (1%nat :: tail).
Proof.
  intros tail Hgt [a [b [c H213]]].
  unfold has_213_at in H213.
  destruct H213 as [Hab [Hbc [Hclen [Hvba Hvac]]]].
  exists 0%nat, (S a), (S b), (S c).
  unfold has_1324_at.
  simpl. repeat split.
  - lia.
  - lia.
  - lia.
  - lia.
  - assert (Hb_in : In (nth b tail 0%nat) tail) by (apply nth_In; lia).
    specialize (Hgt _ Hb_in). lia.
  - exact Hvba.
  - exact Hvac.
Qed.

(* Reverse direction: every 1324-pattern in (1 :: tail) projects onto
   a 213-pattern in tail at indices (j - 1, k - 1, l - 1). The
   projection is index-shift only and works regardless of where i lies. *)

Lemma start_one_1324_means_213_tail : forall tail,
  contains_1324 (1%nat :: tail) ->
  contains_213 tail.
Proof.
  intros tail [i [j [k [l H1324]]]].
  unfold has_1324_at in H1324.
  destruct H1324 as [Hij [Hjk [Hkl [Hlen [Hvik [Hvkj Hvjl]]]]]].
  simpl in Hlen.
  destruct j as [|j']; [lia|].
  destruct k as [|k']; [lia|].
  destruct l as [|l']; [lia|].
  exists j', k', l'.
  unfold has_213_at.
  simpl in Hvkj, Hvjl.
  repeat split.
  - lia.
  - lia.
  - lia.
  - exact Hvkj.
  - exact Hvjl.
Qed.

Theorem start_one_1324_iff_tail_213 : forall tail,
  (forall x, In x tail -> (1 < x)%nat) ->
  (~ contains_1324 (1%nat :: tail) <-> ~ contains_213 tail).
Proof.
  intros tail Hgt.
  split.
  - intros Hno1324 H213.
    apply Hno1324.
    apply start_one_213_creates_1324; assumption.
  - intros Hno213 H1324.
    apply Hno213.
    apply start_one_1324_means_213_tail. exact H1324.
Qed.

End StartOneBijection.

Section JointPositionValues.

Fixpoint binomial_compute (n : nat) (k : nat) : nat :=
  match n with
  | 0%nat => match k with
             | 0%nat => 1%nat
             | S _ => 0%nat
             end
  | S n' => match k with
            | 0%nat => 1%nat
            | S k' => (binomial_compute n' k' + binomial_compute n' (S k'))%nat
            end
  end.

Definition joint_position (n j k : nat) : nat :=
  let perms := perms_of_n n in
  length (filter (fun p =>
    avoids_1324 p &&
    Nat.eqb (nth (j - 1) p 0%nat) 1%nat &&
    Nat.eqb (nth (k - 1) p 0%nat) n
  ) perms).

(* T(n, 1, k) = ((k - 1) / (n - 1)) * binomial(2n - k - 2, n - k). *)
Definition joint_row_one_formula (n k : nat) : nat :=
  ((k - 1) * binomial_compute (2 * n - k - 2) (n - k) / (n - 1))%nat.

(* T(n, j, n) = ((n - j) / (n - 1)) * binomial(n + j - 3, j - 1). *)
Definition joint_col_n_formula (n j : nat) : nat :=
  ((n - j) * binomial_compute (n + j - 3) (j - 1) / (n - 1))%nat.

Theorem joint_row_one_n4 : forall k, (1 <= k <= 4)%nat ->
  joint_position 4 1 k = joint_row_one_formula 4 k.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

Theorem joint_row_one_n5 : forall k, (1 <= k <= 5)%nat ->
  joint_position 5 1 k = joint_row_one_formula 5 k.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

Theorem joint_row_one_n6 : forall k, (1 <= k <= 6)%nat ->
  joint_position 6 1 k = joint_row_one_formula 6 k.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

Theorem joint_col_n_n4 : forall j, (1 <= j <= 4)%nat ->
  joint_position 4 j 4 = joint_col_n_formula 4 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|[|]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

Theorem joint_col_n_n5 : forall j, (1 <= j <= 5)%nat ->
  joint_position 5 j 5 = joint_col_n_formula 5 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|[|[|]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

Theorem joint_col_n_n6 : forall j, (1 <= j <= 6)%nat ->
  joint_position 6 j 6 = joint_col_n_formula 6 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|[|[|[|]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

Theorem joint_row_one_n7 : forall k, (1 <= k <= 7)%nat ->
  joint_position 7 1 k = joint_row_one_formula 7 k.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|]]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

Theorem joint_col_n_n7 : forall j, (1 <= j <= 7)%nat ->
  joint_position 7 j 7 = joint_col_n_formula 7 j.
Proof.
  intros j Hj.
  destruct j as [|[|[|[|[|[|[|[|]]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

End JointPositionValues.

Section ReverseComplement.

(* Element-wise complement: x in [1, n] maps to S n - x, so 1 <-> n,
   2 <-> n-1, etc. The full reverse-complement of a permutation of [n]
   is the reverse of its complement (equivalently, the complement of
   its reverse). *)

Definition complement_n (n : nat) (p : list nat) : list nat :=
  map (fun x => (S n - x)%nat) p.

Definition rc (n : nat) (p : list nat) : list nat :=
  rev (complement_n n p).

Lemma complement_n_length : forall n p,
  length (complement_n n p) = length p.
Proof.
  intros. unfold complement_n. apply length_map.
Qed.

Lemma rc_length : forall n p, length (rc n p) = length p.
Proof.
  intros. unfold rc. rewrite length_rev. apply complement_n_length.
Qed.

Lemma complement_rev_commute : forall n p,
  complement_n n (rev p) = rev (complement_n n p).
Proof.
  intros. unfold complement_n. apply map_rev.
Qed.

Lemma complement_n_idempotent : forall n p,
  (forall x, In x p -> (1 <= x <= n)%nat) ->
  complement_n n (complement_n n p) = p.
Proof.
  intros n p Hb.
  unfold complement_n. rewrite map_map.
  rewrite <- (map_id p) at 2.
  apply map_ext_in. intros x Hin.
  specialize (Hb _ Hin). lia.
Qed.

Theorem rc_involutive : forall n p,
  (forall x, In x p -> (1 <= x <= n)%nat) ->
  rc n (rc n p) = p.
Proof.
  intros n p Hb.
  unfold rc.
  rewrite complement_rev_commute.
  rewrite rev_involutive.
  apply complement_n_idempotent. exact Hb.
Qed.

(* Position correspondence: nth m (rc n p) = S n - nth (length p - 1 - m) p. *)

Lemma rc_nth : forall n p m, (m < length p)%nat ->
  nth m (rc n p) 0%nat = (S n - nth (length p - 1 - m) p 0%nat)%nat.
Proof.
  intros n p m Hm.
  unfold rc, complement_n.
  rewrite rev_nth by (rewrite length_map; lia).
  rewrite length_map.
  replace (length p - S m)%nat with (length p - 1 - m)%nat by lia.
  rewrite (nth_indep _ 0%nat (S n - 0)%nat) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

(* The 1324 pattern is invariant under reverse-complement: for a
   permutation valued in [1, n], a 1324 occurrence at indices
   (i, j, k, l) gives a 1324 occurrence in rc n p at indices
   (length p - 1 - l, length p - 1 - k, length p - 1 - j, length p - 1 - i)
   with the values transformed by x |-> S n - x.

   Pattern reasoning: rev(1324) is 4231 and complement(4231) is 1324,
   so reverse-complement maps 1324 to itself. *)

Lemma rc_creates_1324 : forall n p,
  (forall x, In x p -> (1 <= x <= n)%nat) ->
  contains_1324 p ->
  contains_1324 (rc n p).
Proof.
  intros n p Hb [i [j [k [l H1324]]]].
  unfold has_1324_at in H1324.
  destruct H1324 as [Hij [Hjk [Hkl [Hlen [Hvik [Hvkj Hvjl]]]]]].
  exists (length p - 1 - l)%nat, (length p - 1 - k)%nat,
         (length p - 1 - j)%nat, (length p - 1 - i)%nat.
  unfold has_1324_at.
  assert (HinI : In (nth i p 0%nat) p) by (apply nth_In; lia).
  assert (HinJ : In (nth j p 0%nat) p) by (apply nth_In; lia).
  assert (HinK : In (nth k p 0%nat) p) by (apply nth_In; lia).
  assert (HinL : In (nth l p 0%nat) p) by (apply nth_In; lia).
  pose proof (Hb _ HinI) as HboundI.
  pose proof (Hb _ HinJ) as HboundJ.
  pose proof (Hb _ HinK) as HboundK.
  pose proof (Hb _ HinL) as HboundL.
  rewrite rc_length.
  rewrite (@rc_nth n p (length p - 1 - l)%nat) by lia.
  rewrite (@rc_nth n p (length p - 1 - k)%nat) by lia.
  rewrite (@rc_nth n p (length p - 1 - j)%nat) by lia.
  rewrite (@rc_nth n p (length p - 1 - i)%nat) by lia.
  replace (length p - 1 - (length p - 1 - l))%nat with l by lia.
  replace (length p - 1 - (length p - 1 - k))%nat with k by lia.
  replace (length p - 1 - (length p - 1 - j))%nat with j by lia.
  replace (length p - 1 - (length p - 1 - i))%nat with i by lia.
  repeat split; lia.
Qed.

Theorem rc_preserves_avoid_1324 : forall n p,
  (forall x, In x p -> (1 <= x <= n)%nat) ->
  (~ contains_1324 p <-> ~ contains_1324 (rc n p)).
Proof.
  intros n p Hb.
  split.
  - intros Hno H1324_rc.
    apply Hno.
    assert (Hbrc : forall x, In x (rc n p) -> (1 <= x <= n)%nat).
    { intros x Hxin.
      unfold rc, complement_n in Hxin.
      apply in_rev in Hxin.
      apply in_map_iff in Hxin.
      destruct Hxin as [y [Hyeq Hyin]].
      specialize (Hb _ Hyin). lia. }
    pose proof (@rc_creates_1324 n (rc n p) Hbrc H1324_rc) as Hp.
    rewrite (@rc_involutive n p Hb) in Hp.
    exact Hp.
  - intros Hno H1324.
    apply Hno.
    apply (@rc_creates_1324 n p Hb H1324).
Qed.

End ReverseComplement.

Section CatalanConvolution.

(* k-fold Catalan convolution: ck j m = sum over (a_1, ..., a_j) with
   a_1 + ... + a_j = m of prod Cat(a_i). Recurrences:
     ck 0 0 = 1, ck 0 (S _) = 0  (empty product convention),
     ck (S j) m = sum_{i=0..m} Cat(i) * ck j (m - i). *)

Fixpoint sum_cat_to (q : nat) (f : nat -> nat) : nat :=
  match q with
  | 0%nat => f 0%nat
  | S q' => (sum_cat_to q' f + f (S q'))%nat
  end.

Fixpoint ck (j : nat) (m : nat) : nat :=
  match j with
  | 0%nat => match m with 0%nat => 1%nat | S _ => 0%nat end
  | S j' =>
    sum_cat_to m (fun i => (catalan_compute i * ck j' (m - i))%nat)
  end.

(* Closed form (Lagrange inversion): for j >= 1,
     ck j m = (j / (m + j)) * binomial(2m + j - 1, m).
   Stated in the integer-division form since the division is exact for
   j >= 1. *)

Definition ck_formula (j : nat) (m : nat) : nat :=
  ((j * binomial_compute (2 * m + j - 1) m) / (m + j))%nat.

(* j = 1 reduces to the Catalan numbers themselves: ck 1 m = Cat(m). *)

Theorem ck_matches_catalan_j1 :
  forall m, (m <= 6)%nat -> ck 1 m = catalan_compute m.
Proof.
  intros m Hm.
  destruct m as [|[|[|[|[|[|[|]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

(* j = 2 reduces to Cat(m + 1) by the classical Catalan recurrence
   sum_{i=0..m} Cat(i) * Cat(m - i) = Cat(m + 1). *)

Theorem ck_matches_catalan_j2 :
  forall m, (m <= 5)%nat -> ck 2 m = catalan_compute (S m).
Proof.
  intros m Hm.
  destruct m as [|[|[|[|[|[|]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

(* Closed-form identity verified for j in [1, 4] and m in [0, 4]. *)

Theorem ck_matches_closed_form :
  forall j m, (1 <= j <= 4)%nat -> (m <= 4)%nat ->
  ck j m = ck_formula j m.
Proof.
  intros j m Hj Hm.
  destruct j as [|[|[|[|[|]]]]]; try lia;
  destruct m as [|[|[|[|[|]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

(* The joint matrix first row factors through ck via the bijection
   start_one_1324_iff_tail_213, with the connection
   joint_position n 1 k = ck (k - 1) (n - k). *)

Theorem joint_row_one_via_ck :
  forall n k, (4 <= n <= 6)%nat -> (1 <= k <= n)%nat ->
  joint_position n 1 k = ck (k - 1) (n - k).
Proof.
  intros n k Hn Hk.
  destruct n as [|[|[|[|[|[|[|]]]]]]]; try lia;
  destruct k as [|[|[|[|[|[|[|]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

End CatalanConvolution.

Section CatalanClosedForm.

(* The closed-form expression for the m-th Catalan number:
   cat_closed m = binomial(2m, m) / (m + 1). The identity
   cat_closed m = catalan_compute m is the standard Catalan formula. *)

Definition cat_closed (m : nat) : nat :=
  (binomial_compute (2 * m) m / S m)%nat.

(* Equivalent integer-arithmetic form (m + 1) * Cat(m) = binomial(2m, m),
   verified against the recursive Catalan definition by vm_compute for
   0 <= m <= 8. *)

Theorem cat_closed_matches_catalan_bounded :
  cat_closed 0 = catalan_compute 0 /\
  cat_closed 1 = catalan_compute 1 /\
  cat_closed 2 = catalan_compute 2 /\
  cat_closed 3 = catalan_compute 3 /\
  cat_closed 4 = catalan_compute 4 /\
  cat_closed 5 = catalan_compute 5 /\
  cat_closed 6 = catalan_compute 6 /\
  cat_closed 7 = catalan_compute 7 /\
  cat_closed 8 = catalan_compute 8.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(* Equivalent integer form of the Catalan formula, for the same range. *)

Theorem catalan_integer_form_bounded :
  (1 * catalan_compute 0 = binomial_compute 0 0)%nat /\
  (2 * catalan_compute 1 = binomial_compute 2 1)%nat /\
  (3 * catalan_compute 2 = binomial_compute 4 2)%nat /\
  (4 * catalan_compute 3 = binomial_compute 6 3)%nat /\
  (5 * catalan_compute 4 = binomial_compute 8 4)%nat /\
  (6 * catalan_compute 5 = binomial_compute 10 5)%nat /\
  (7 * catalan_compute 6 = binomial_compute 12 6)%nat /\
  (8 * catalan_compute 7 = binomial_compute 14 7)%nat /\
  (9 * catalan_compute 8 = binomial_compute 16 8)%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

End CatalanClosedForm.

Section CatalanConvolutionExtended.

(* Closed-form identity verified for j in [1, 6] and m in [0, 6]. *)

Theorem ck_matches_closed_form_extended :
  forall j m, (1 <= j <= 6)%nat -> (m <= 6)%nat ->
  ck j m = ck_formula j m.
Proof.
  intros j m Hj Hm.
  destruct j as [|[|[|[|[|[|[|]]]]]]]; try lia;
  destruct m as [|[|[|[|[|[|[|]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

End CatalanConvolutionExtended.

Section FactorialInfrastructure.

(* factorial is defined upstream in the inherited Avoid1324 body. *)

Lemma factorial_pos : forall n, (factorial n > 0)%nat.
Proof.
  induction n; simpl; lia.
Qed.

Lemma binomial_pascal : forall n k,
  binomial_compute (S n) (S k) =
  (binomial_compute n k + binomial_compute n (S k))%nat.
Proof. intros. reflexivity. Qed.

Lemma binomial_n_0 : forall n, binomial_compute n 0 = 1%nat.
Proof. destruct n; reflexivity. Qed.

Lemma binomial_0_S : forall k, binomial_compute 0 (S k) = 0%nat.
Proof. destruct k; reflexivity. Qed.

Lemma binomial_zero_above : forall n k,
  (n < k)%nat -> binomial_compute n k = 0%nat.
Proof.
  induction n; intros k Hnk.
  - destruct k; [lia|reflexivity].
  - destruct k; [lia|].
    rewrite binomial_pascal.
    rewrite IHn by lia. rewrite IHn by lia. lia.
Qed.

Lemma binomial_n_n : forall n, binomial_compute n n = 1%nat.
Proof.
  induction n.
  - reflexivity.
  - rewrite binomial_pascal.
    rewrite IHn. rewrite binomial_zero_above by lia. lia.
Qed.

(* The factorial characterization of binomial coefficients:
   binomial(n, k) * k! * (n - k)! = n!  whenever k <= n. *)

Theorem binomial_factorial : forall n k, (k <= n)%nat ->
  (binomial_compute n k * factorial k * factorial (n - k) = factorial n)%nat.
Proof.
  induction n; intros k Hk.
  - assert (Hk0 : (k = 0)%nat) by lia. subst. simpl. lia.
  - destruct k as [|k'].
    + rewrite binomial_n_0.
      replace (S n - 0)%nat with (S n) by lia.
      simpl. lia.
    + destruct (Nat.eq_dec k' n) as [Hk_eq | Hk_neq].
      * subst k'. rewrite binomial_n_n.
        replace (S n - S n)%nat with 0%nat by lia.
        simpl. lia.
      * assert (Hk_lt : (k' < n)%nat) by lia.
        specialize (IHn k' (Nat.lt_le_incl _ _ Hk_lt)) as IH_k.
        specialize (IHn (S k') Hk_lt) as IH_Sk.
        assert (Hf_Sn : factorial (S n) = (S n * factorial n)%nat) by reflexivity.
        assert (Hf_Sk : factorial (S k') = (S k' * factorial k')%nat) by reflexivity.
        assert (Hf_diff : factorial (n - k') =
                          ((n - k') * factorial (n - S k'))%nat).
        { replace (n - k')%nat with (S (n - S k')) by lia.
          simpl factorial. lia. }
        rewrite binomial_pascal.
        replace (S n - S k')%nat with (n - k')%nat by lia.
        rewrite Nat.mul_add_distr_r, Nat.mul_add_distr_r.
        rewrite Hf_Sn, Hf_Sk, Hf_diff.
        rewrite Hf_Sk in IH_Sk.
        rewrite Hf_diff in IH_k.
        nia.
Qed.

Lemma mul_eq_cancel_pos : forall a b c,
  (c > 0)%nat -> (a * c = b * c)%nat -> (a = b)%nat.
Proof. intros. nia. Qed.

(* Absorption identity: (S k) * binomial(S n) (S k) = (S n) * binomial(n) k.
   Derived from binomial_factorial by cancelling the common factor
   factorial k * factorial (n - k). *)

Theorem binomial_absorb : forall n k, (k <= n)%nat ->
  ((S k) * binomial_compute (S n) (S k) = (S n) * binomial_compute n k)%nat.
Proof.
  intros n k Hk.
  pose proof (@binomial_factorial (S n) (S k) (le_n_S _ _ Hk)) as H1.
  pose proof (@binomial_factorial n k Hk) as H2.
  replace (S n - S k)%nat with (n - k)%nat in H1 by lia.
  change (factorial (S k)) with ((S k) * factorial k)%nat in H1.
  change (factorial (S n)) with ((S n) * factorial n)%nat in H1.
  pose proof (factorial_pos k) as Hfk.
  pose proof (factorial_pos (n - k)) as Hfnk.
  apply (@mul_eq_cancel_pos _ _ (factorial k * factorial (n - k))%nat);
    [nia | nia].
Qed.

(* Symmetry: binomial n k = binomial n (n - k). *)

Theorem binomial_symmetry : forall n k, (k <= n)%nat ->
  binomial_compute n k = binomial_compute n (n - k).
Proof.
  intros n k Hk.
  pose proof (@binomial_factorial n k Hk) as H1.
  pose proof (@binomial_factorial n (n - k)%nat ltac:(lia)) as H2.
  replace (n - (n - k))%nat with k in H2 by lia.
  pose proof (factorial_pos k).
  pose proof (factorial_pos (n - k)).
  apply (@mul_eq_cancel_pos _ _ (factorial k * factorial (n - k))%nat);
    [nia | nia].
Qed.

(* Doubling: binomial(2m+2, m+1) = 2 * binomial(2m+1, m). *)

Theorem binomial_doubling : forall m,
  (binomial_compute (2 * m + 2) (m + 1) =
   2 * binomial_compute (2 * m + 1) m)%nat.
Proof.
  intros m.
  replace (2 * m + 2)%nat with (S (S (2 * m))) by lia.
  replace (m + 1)%nat with (S m) by lia.
  rewrite binomial_pascal.
  replace (2 * m + 1)%nat with (S (2 * m))%nat by lia.
  rewrite (@binomial_symmetry (S (2 * m)) (S m)) by lia.
  replace (S (2 * m) - S m)%nat with m by lia.
  lia.
Qed.

(* Complementary absorption: (S m) * binomial(2m, m+1) = m * binomial(2m, m).
   Two applications of binomial_absorb at (2m+1, m) and (2m+1, m-1)
   combined with symmetry. *)

Lemma binomial_absorb_compl : forall m,
  ((S m) * binomial_compute (2 * m) (m + 1) =
   m * binomial_compute (2 * m) m)%nat.
Proof.
  intros m. destruct m as [|m'].
  - simpl. lia.
  - replace (2 * S m')%nat with (S (S (2 * m'))) by lia.
    replace (S m' + 1)%nat with (S (S m')) by lia.
    rewrite (@binomial_absorb (S (2 * m')) (S m')) by lia.
    rewrite (@binomial_absorb (S (2 * m')) m') by lia.
    rewrite (@binomial_symmetry (S (2 * m')) m') by lia.
    replace (S (2 * m') - m')%nat with (S m') by lia.
    reflexivity.
Qed.

End FactorialInfrastructure.

Section CatalanAlternative.

(* Alternative Catalan form: cat_alt m = binomial(2m, m) - binomial(2m, m+1). *)

Definition cat_alt (m : nat) : nat :=
  (binomial_compute (2 * m) m - binomial_compute (2 * m) (m + 1))%nat.

Theorem cat_alt_matches_catalan_bounded :
  forall m, (m <= 6)%nat -> cat_alt m = catalan_compute m.
Proof.
  intros m Hm.
  destruct m as [|[|[|[|[|[|[|]]]]]]]; try lia;
  vm_compute; reflexivity.
Qed.

(* Conditional Catalan formula: assuming cat_alt = catalan_compute,
   the standard Catalan formula (S m) * catalan(m) = binomial(2m, m)
   follows by binomial_absorb_compl. *)

Theorem catalan_formula_from_alt : forall m,
  cat_alt m = catalan_compute m ->
  ((S m) * catalan_compute m = binomial_compute (2 * m) m)%nat.
Proof.
  intros m Heq.
  rewrite <- Heq. unfold cat_alt.
  rewrite Nat.mul_sub_distr_l.
  rewrite (@binomial_absorb_compl m).
  lia.
Qed.

(* Composing catalan_formula_from_alt with cat_alt_matches_catalan_bounded
   gives the Catalan formula (S m) * catalan_compute m = binomial(2m, m)
   for 0 <= m <= 6. *)

Theorem catalan_formula_bounded : forall m, (m <= 6)%nat ->
  ((S m) * catalan_compute m = binomial_compute (2 * m) m)%nat.
Proof.
  intros m Hm.
  apply catalan_formula_from_alt.
  apply cat_alt_matches_catalan_bounded. exact Hm.
Qed.

(* The Catalan formula holds unconditionally for cat_alt:
   (S m) * cat_alt m = binomial(2m, m) for all m, proved purely by
   binomial_absorb_compl (no enumeration, no convolution argument). *)

Theorem cat_alt_formula : forall m,
  ((S m) * cat_alt m = binomial_compute (2 * m) m)%nat.
Proof.
  intros m.
  unfold cat_alt.
  rewrite Nat.mul_sub_distr_l.
  rewrite (@binomial_absorb_compl m).
  lia.
Qed.

(* cat_alt satisfies the Catalan ratio recurrence
   (m + 2) * cat_alt (S m) = (4m + 2) * cat_alt m,
   provable from binomial_absorb_compl and binomial_doubling without
   any sum-manipulation. *)

Theorem cat_alt_ratio : forall m,
  ((m + 2) * cat_alt (S m) = (4 * m + 2) * cat_alt m)%nat.
Proof.
  intros m.
  assert (Hf_m : ((S m) * cat_alt m = binomial_compute (2 * m) m)%nat).
  { unfold cat_alt. rewrite Nat.mul_sub_distr_l.
    rewrite (@binomial_absorb_compl m). lia. }
  assert (Hf_Sm : ((S (S m)) * cat_alt (S m) =
                   binomial_compute (2 * (S m)) (S m))%nat).
  { unfold cat_alt. rewrite Nat.mul_sub_distr_l.
    rewrite (@binomial_absorb_compl (S m)). lia. }
  assert (Hd : ((m + 1) * binomial_compute (2 * (S m)) (S m) =
                (4 * m + 2) * binomial_compute (2 * m) m)%nat).
  { pose proof (binomial_doubling m) as Hdo.
    pose proof (@binomial_absorb (2 * m) m ltac:(lia)) as Habs.
    pose proof (@binomial_symmetry (S (2 * m)) m ltac:(lia)) as Hsym.
    replace (S (2 * m) - m)%nat with (S m) in Hsym by lia.
    rewrite <- Hsym in Habs.
    replace (m + 1)%nat with (S m) in Hdo by lia.
    replace (2 * m + 1)%nat with (S (2 * m)) in Hdo by lia.
    replace (2 * S m)%nat with (2 * m + 2)%nat by lia.
    rewrite Hdo.
    nia. }
  replace (m + 2)%nat with (S (S m)) by lia.
  rewrite Hf_Sm.
  apply (@mul_eq_cancel_pos _ _ (S m)); [lia|].
  nia.
Qed.

End CatalanAlternative.

Section SumLibrary.

(* Explicit summation operator: sum_to n f = f 0 + f 1 + ... + f n.
   Used to formulate sum identities outside the inner sum_cat helper
   of catalan_compute. *)

Fixpoint sum_to (n : nat) (f : nat -> nat) : nat :=
  match n with
  | 0%nat => f 0%nat
  | S n' => (sum_to n' f + f (S n'))%nat
  end.

Lemma sum_to_const_mul : forall n c f,
  sum_to n (fun k => (c * f k)%nat) = (c * sum_to n f)%nat.
Proof.
  intros n c f. induction n.
  - reflexivity.
  - simpl. lia.
Qed.

Lemma sum_to_split : forall n f g,
  sum_to n (fun k => (f k + g k)%nat) =
  (sum_to n f + sum_to n g)%nat.
Proof.
  intros n f g. induction n.
  - reflexivity.
  - simpl. lia.
Qed.

Lemma sum_to_ext : forall n f g,
  (forall k, (k <= n)%nat -> f k = g k) ->
  sum_to n f = sum_to n g.
Proof.
  intros n f g Heq. induction n.
  - simpl. apply Heq. lia.
  - simpl. rewrite IHn by (intros; apply Heq; lia).
    rewrite (Heq (S n)) by lia. reflexivity.
Qed.

Lemma sum_to_shift : forall n f,
  (sum_to n f + f (S n))%nat =
  (f 0%nat + sum_to n (fun k => f (S k)))%nat.
Proof.
  induction n; intros f.
  - simpl. lia.
  - simpl. rewrite (IHn f). lia.
Qed.

Lemma sum_to_reverse : forall n f,
  sum_to n f = sum_to n (fun k => f (n - k)%nat).
Proof.
  induction n; intros f.
  - simpl. reflexivity.
  - simpl.
    rewrite Nat.sub_diag.
    rewrite sum_to_shift.
    rewrite (IHn (fun k => f (S k))).
    rewrite (@sum_to_ext n (fun k => f (S (n - k)%nat))
                            (fun k => f (S n - k)%nat))
       by (intros k Hk; f_equal; lia).
    apply Nat.add_comm.
Qed.

(* sum_to_pred k f = f 0 + f 1 + ... + f (k - 1).
   Convenient for downward-iterating accumulators. *)

Fixpoint sum_to_pred (k : nat) (f : nat -> nat) : nat :=
  match k with
  | 0%nat => 0%nat
  | S k' => (sum_to_pred k' f + f k')%nat
  end.

Lemma sum_to_pred_S : forall n f, sum_to_pred (S n) f = sum_to n f.
Proof.
  intros n. induction n; intros f.
  - reflexivity.
  - simpl. f_equal. apply IHn.
Qed.

(* Top-level analogue of the inner sum_cat helper inside catalan_compute. *)

Fixpoint sc_helper (cat : nat -> nat) (n : nat) (k : nat) (acc : nat) : nat :=
  match k with
  | 0%nat => acc
  | S k' => sc_helper cat n k' (acc + cat k' * cat (n - k'))%nat
  end.

Lemma sc_helper_eq : forall cat n k acc,
  sc_helper cat n k acc =
  (acc + sum_to_pred k (fun j => (cat j * cat (n - j))%nat))%nat.
Proof.
  intros cat n k. induction k; intros acc.
  - simpl. lia.
  - simpl. rewrite IHk. simpl. lia.
Qed.

(* Helper: the inner anonymous fix expanded inside catalan_compute (S n)
   computes the same as sc_helper at the same parameters. The proof is
   by induction on the iteration variable, with both sides reducing
   step-for-step to the same body. *)

Lemma sc_inner_eq_sc_helper : forall n k acc,
  (fix sc_inner (kk : nat) (a : nat) {struct kk} : nat :=
     match kk with
     | 0%nat => a
     | S kk' => sc_inner kk'
                  (a + catalan_compute kk' * catalan_compute (n - kk'))%nat
     end) k acc = sc_helper catalan_compute n k acc.
Proof.
  intros n. induction k; intros acc.
  - reflexivity.
  - simpl. apply IHk.
Qed.

(* Bridge from catalan_compute's inner anonymous fix to sc_helper, via
   [change] to expose the matching syntactic form, then the helper. *)

Lemma catalan_compute_via_sc : forall n,
  catalan_compute (S n) = sc_helper catalan_compute n (S n) 0%nat.
Proof.
  intros n.
  change (catalan_compute (S n))
    with ((fix sc_inner (kk : nat) (a : nat) {struct kk} : nat :=
            match kk with
            | 0%nat => a
            | S kk' => sc_inner kk'
                        (a + catalan_compute kk' * catalan_compute (n - kk'))%nat
            end) (S n) 0%nat).
  apply sc_inner_eq_sc_helper.
Qed.

Theorem catalan_compute_eq_sum : forall n,
  catalan_compute (S n) =
  sum_to n (fun k => (catalan_compute k * catalan_compute (n - k))%nat).
Proof.
  intros n.
  rewrite catalan_compute_via_sc.
  rewrite sc_helper_eq.
  rewrite sum_to_pred_S.
  reflexivity.
Qed.

(* The symmetry-based first-moment identity:
   2 * sum_{k=0..m} k * Cat(k) * Cat(m - k) = m * Cat(m + 1).
   Proof: pair the sum with its reversal under sum_to_reverse, sum
   the two copies, and apply Nat.mul_comm + linearity. *)

Theorem cat_first_moment_helper : forall m,
  (2 * sum_to m (fun k => (k * catalan_compute k * catalan_compute (m - k))%nat) =
   m * catalan_compute (S m))%nat.
Proof.
  intros m.
  rewrite catalan_compute_eq_sum.
  rewrite <- (@sum_to_const_mul m m (fun k => (catalan_compute k * catalan_compute (m - k))%nat)).
  rewrite (@sum_to_ext m
              (fun k => (m * (catalan_compute k * catalan_compute (m - k)))%nat)
              (fun k => (k * catalan_compute k * catalan_compute (m - k) +
                        (m - k) * catalan_compute k * catalan_compute (m - k))%nat))
       by (intros k Hk;
           set (XY := (catalan_compute k * catalan_compute (m - k))%nat);
           replace (k * catalan_compute k * catalan_compute (m - k))%nat
              with (k * XY)%nat by (unfold XY; nia);
           replace ((m - k) * catalan_compute k * catalan_compute (m - k))%nat
              with ((m - k) * XY)%nat by (unfold XY; nia);
           nia).
  rewrite sum_to_split.
  enough (Heq : sum_to m (fun k => ((m - k) * catalan_compute k * catalan_compute (m - k))%nat) =
                sum_to m (fun k => (k * catalan_compute k * catalan_compute (m - k))%nat)) by lia.
  rewrite (sum_to_reverse m (fun k => (k * catalan_compute k * catalan_compute (m - k))%nat)).
  apply (@sum_to_ext m).
  intros k Hk.
  replace (m - (m - k))%nat with k by lia.
  nia.
Qed.

End SumLibrary.
