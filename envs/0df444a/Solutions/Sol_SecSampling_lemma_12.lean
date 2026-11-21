-- Prove2me | solution 1 for SecSampling.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:17:13.211475+00:00
-- url     : https://prove2.me/submissions/95c391b8-0d02-46ec-9623-e26eeced1f81

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace Aux_SecSampling_lemma_12

open SecSampling

theorem ct_false_cons (l : List Bool) : List.count true (false :: l) = List.count true l :=
  List.count_cons_of_ne (by decide)

theorem cf_false_cons (l : List Bool) : List.count false (false :: l) = List.count false l + 1 :=
  List.count_cons_self

theorem ct_of_nf (l : List Bool) (h : false ∉ l) : l.count true = l.length :=
  List.count_eq_length.mpr (fun b hb => by
    cases b
    · exact absurd hb h
    · rfl)

theorem ct_add_cf (l : List Bool) : l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · rw [ct_false_cons, cf_false_cons, List.length_cons]; omega
    · rw [List.count_cons_self, List.count_cons_of_ne (by decide), List.length_cons]; omega

theorem all_of_nf (l : List Bool) (h : false ∉ l) : ∀ b ∈ l, b = true := fun b hb => by
  cases b
  · exact absurd hb h
  · rfl

theorem eq_of_nf (A B : List Bool) (hA : false ∉ A) (hB : false ∉ B)
    (hl : A.length = B.length) : A = B := by
  have e1 : A = List.replicate A.length true := List.eq_replicate_iff.mpr ⟨rfl, all_of_nf A hA⟩
  have e2 : B = List.replicate B.length true := List.eq_replicate_iff.mpr ⟨rfl, all_of_nf B hB⟩
  calc A = List.replicate A.length true := e1
    _ = List.replicate B.length true := by rw [hl]
    _ = B := e2.symm

theorem idx_lemma (T R : List Bool) (h : false ∉ T) :
    (T ++ false :: R).idxOf false = T.length := by
  rw [List.idxOf_append, if_neg h, List.idxOf_cons_self]
  omega

theorem lz_eq (P T : List Bool) (hT : false ∉ T) : lastZero (P ++ false :: T) = P.length + 1 := by
  unfold lastZero
  rw [if_pos (show false ∈ P ++ false :: T by simp)]
  have hrev : (P ++ false :: T).reverse = T.reverse ++ false :: P.reverse := by simp
  have hT' : false ∉ T.reverse := by rw [List.mem_reverse]; exact hT
  rw [hrev, idx_lemma _ _ hT']
  simp only [List.length_append, List.length_cons, List.length_reverse]
  omega

theorem decomp (I : List Bool) (h : false ∈ I) : ∃ P T, false ∉ T ∧ I = P ++ false :: T := by
  induction I with
  | nil => simp at h
  | cons a I ih =>
    by_cases h' : false ∈ I
    · obtain ⟨P, T, hT, hI⟩ := ih h'
      exact ⟨a :: P, T, hT, by rw [hI, List.cons_append]⟩
    · have ha : a = false := by
        rcases List.mem_cons.mp h with h1 | h1
        · exact h1.symm
        · exact absurd h1 h'
      exact ⟨[], I, h', by rw [ha, List.nil_append]⟩

theorem tk (Q R : List Bool) (x : Bool) : (Q ++ x :: R).take (Q.length + 1) = Q ++ [x] := by
  induction Q with
  | nil => rfl
  | cons a Q ih =>
    simp only [List.cons_append, List.length_cons, List.take_succ_cons, ih]

theorem core (X Y : List Bool) (hc : Conflict X Y) (hl : Y.length = X.length + 1) :
    ∃ Q A B, false ∉ A ∧ false ∉ B ∧ X = Q ++ false :: (A ++ B) ∧
      Y = Q ++ false :: (A ++ false :: B) := by
  obtain ⟨_, hX, _, hbn, htk⟩ := hc
  obtain ⟨Q, U, hU, rfl⟩ := decomp X hX
  rw [lz_eq Q U hU] at htk
  have e : Y = Q ++ false :: Y.drop (Q.length + 1) := by
    calc Y = Y.take (Q.length + 1) ++ Y.drop (Q.length + 1) := (List.take_append_drop _ _).symm
      _ = Q ++ false :: Y.drop (Q.length + 1) := by
          rw [← htk, tk]
          simp
  obtain ⟨V, hV⟩ : ∃ V, V = Y.drop (Q.length + 1) := ⟨_, rfl⟩
  rw [← hV] at e
  subst e
  have hVl : V.length = U.length + 1 := by
    simp only [List.length_append, List.length_cons] at hl
    omega
  have hcU := ct_of_nf U hU
  have hcV : V.count true = U.length := by
    unfold bitNorm at hbn
    rw [List.count_append, List.count_append, ct_false_cons, ct_false_cons, hcU] at hbn
    omega
  have hfV : V.count false = 1 := by
    have := ct_add_cf V
    omega
  have hfmem : false ∈ V := List.count_pos_iff.mp (by omega)
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hfmem
  rw [List.count_append, cf_false_cons] at hfV
  have hA : false ∉ A := List.count_eq_zero.mp (by omega)
  have hB : false ∉ B := List.count_eq_zero.mp (by omega)
  have hAB : false ∉ A ++ B := by
    rw [List.mem_append]
    rintro (h | h)
    · exact hA h
    · exact hB h
  have hUAB : U = A ++ B := eq_of_nf U (A ++ B) hU hAB (by
    simp only [List.length_append, List.length_cons] at hVl ⊢
    omega)
  exact ⟨Q, A, B, hA, hB, by rw [hUAB], rfl⟩

/-! ### Replicate forms -/

theorem nf_rep (A : List Bool) (h : false ∉ A) : A = List.replicate A.length true :=
  List.eq_replicate_iff.mpr ⟨rfl, all_of_nf A h⟩

theorem nf_replicate (t : ℕ) : false ∉ List.replicate t true := by
  simp [List.mem_replicate]

theorem lzR (Q : List Bool) (t : ℕ) :
    lastZero (Q ++ false :: List.replicate t true) = Q.length + 1 :=
  lz_eq Q _ (nf_replicate t)

theorem decompR (I : List Bool) (h : false ∈ I) :
    ∃ Q t, I = Q ++ false :: List.replicate t true := by
  obtain ⟨P, T, hT, hI⟩ := decomp I h
  exact ⟨P, T.length, by rw [hI, ← nf_rep T hT]⟩

theorem uniqR {Q Q' : List Bool} {t t' : ℕ}
    (h : Q ++ false :: List.replicate t true = Q' ++ false :: List.replicate t' true) :
    Q = Q' ∧ t = t' := by
  have h1 := congrArg lastZero h
  rw [lzR, lzR] at h1
  have hl : Q.length = Q'.length := by omega
  obtain ⟨hQ, h2⟩ := List.append_inj h hl
  refine ⟨hQ, ?_⟩
  have h3 := congrArg List.length h2
  simpa using h3

theorem ct_rep (t : ℕ) : (List.replicate t true).count true = t := List.count_replicate_self

theorem coreR (X Y : List Bool) (hc : Conflict X Y) (hl : Y.length = X.length + 1) :
    ∃ Q a b, X = Q ++ false :: List.replicate (a + b) true ∧
      Y = Q ++ false :: (List.replicate a true ++ false :: List.replicate b true) := by
  obtain ⟨Q, A, B, hA, hB, h1, h2⟩ := core X Y hc hl
  refine ⟨Q, A.length, B.length, ?_, ?_⟩
  · rw [h1, List.replicate_add, ← nf_rep A hA, ← nf_rep B hB]
  · rw [h2, ← nf_rep A hA, ← nf_rep B hB]

theorem conflictR (Q : List Bool) (a b : ℕ) :
    Conflict (Q ++ false :: List.replicate (a + b) true)
      (Q ++ false :: (List.replicate a true ++ false :: List.replicate b true)) := by
  unfold Conflict
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_replicate]; omega
  · unfold bitNorm
    simp only [List.count_append, ct_false_cons, ct_rep] <;> omega
  · rw [lzR, tk, tk]

theorem edgeR (Q : List Bool) (a b : ℕ) :
    Edge (Q ++ false :: List.replicate (a + b) true)
      (Q ++ false :: (List.replicate a true ++ false :: List.replicate b true)) := by
  unfold Edge
  refine ⟨conflictR Q a b, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_replicate]; omega

theorem mem_strings {n : ℕ} {J : List Bool} : J ∈ strings n ↔ J.length = n := by
  unfold strings
  constructor
  · intro h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · rintro rfl
    exact Finset.mem_image.mpr ⟨fun i => J[i.val], Finset.mem_univ _, List.ofFn_getElem⟩

theorem card_strings (m : ℕ) : (strings m).card = 2 ^ m := by
  unfold strings
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp

open Classical in
theorem degree_nf (I : List Bool) (h : false ∉ I) : degree I = 0 := by
  unfold degree
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro J _ he
  unfold Edge Conflict at he
  exact h he.1.2.1

open Classical in
theorem degreeR (Q : List Bool) (t : ℕ) :
    degree (Q ++ false :: List.replicate t true) = t + 1 := by
  unfold degree
  have hset : (strings ((Q ++ false :: List.replicate t true).length + 1)).filter
      (fun J => Edge (Q ++ false :: List.replicate t true) J) =
      (Finset.range (t + 1)).image
        (fun j => Q ++ false :: (List.replicate j true ++ false :: List.replicate (t - j) true)) := by
    ext J
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, mem_strings]
    constructor
    · rintro ⟨_, he⟩
      unfold Edge at he
      obtain ⟨Q', a, b, h1, h2⟩ := coreR _ _ he.1 he.2
      obtain ⟨hQ, ht⟩ := uniqR h1
      have hb : t - a = b := by omega
      refine ⟨a, by omega, ?_⟩
      rw [h2, ← hQ, hb]
    · rintro ⟨j, hj, rfl⟩
      refine ⟨by simp only [List.length_append, List.length_cons, List.length_replicate]; omega, ?_⟩
      have e : t = j + (t - j) := by omega
      have := edgeR Q j (t - j)
      rw [← e] at this
      exact this
  rw [hset, Finset.card_image_of_injOn, Finset.card_range]
  intro j1 _ j2 _ heq
  have h := List.append_cancel_left heq
  have h2 := (List.cons.inj h).2
  have h3 := congrArg (List.idxOf false) h2
  rw [idx_lemma _ _ (nf_replicate _), idx_lemma _ _ (nf_replicate _)] at h3
  simpa using h3

theorem deg_child (Q : List Bool) (a b : ℕ) :
    degree (Q ++ false :: (List.replicate a true ++ false :: List.replicate b true)) = b + 1 := by
  have e : Q ++ false :: (List.replicate a true ++ false :: List.replicate b true) =
      (Q ++ false :: List.replicate a true) ++ false :: List.replicate b true := by simp
  rw [e, degreeR]


/-! ### Weights -/

theorem cf_rep (k : ℕ) : (List.replicate k true).count false = 0 :=
  List.count_eq_zero.mpr (nf_replicate k)

theorem ct_true_cons (l : List Bool) : List.count true (true :: l) = List.count true l + 1 :=
  List.count_cons_self

theorem cf_true_cons (l : List Bool) : List.count false (true :: l) = List.count false l :=
  List.count_cons_of_ne (by decide)

theorem weight_eq (p : ℝ) (I : List Bool) :
    weight p I = p ^ (I.count true) * (1 - p) ^ (I.count false) := by
  unfold weight bitNorm
  rw [show I.length - I.count true = I.count false by have := ct_add_cf I; omega]

theorem weight_app (p : ℝ) (A : List Bool) (k : ℕ) :
    weight p (A ++ false :: List.replicate k true) = weight p A * ((1 - p) * p ^ k) := by
  rw [weight_eq, weight_eq]
  simp only [List.count_append, ct_false_cons, cf_false_cons, ct_rep, cf_rep]
  ring

theorem weight_child (p : ℝ) (A : List Bool) (a b : ℕ) :
    weight p (A ++ false :: (List.replicate a true ++ false :: List.replicate b true)) =
      weight p A * ((1 - p) * p ^ a * ((1 - p) * p ^ b)) := by
  have e : A ++ false :: (List.replicate a true ++ false :: List.replicate b true) =
      (A ++ false :: List.replicate a true) ++ false :: List.replicate b true := by simp
  rw [e, weight_app, weight_app]
  ring

theorem weight_cons_true (p : ℝ) (A : List Bool) : weight p (true :: A) = p * weight p A := by
  rw [weight_eq, weight_eq, ct_true_cons, cf_true_cons]
  ring

theorem weight_cons_false (p : ℝ) (A : List Bool) :
    weight p (false :: A) = (1 - p) * weight p A := by
  rw [weight_eq, weight_eq, ct_false_cons, cf_false_cons]
  ring

theorem strings_zero : strings 0 = {[]} := by
  ext J
  simp only [mem_strings, Finset.mem_singleton]
  exact List.length_eq_zero_iff

theorem strings_succ (m : ℕ) :
    strings (m + 1) = (strings m).image (List.cons true) ∪ (strings m).image (List.cons false) := by
  ext J
  simp only [Finset.mem_union, Finset.mem_image, mem_strings]
  constructor
  · intro h
    cases J with
    | nil => simp at h
    | cons b A =>
      cases b
      · right; exact ⟨A, by simpa using h, rfl⟩
      · left; exact ⟨A, by simpa using h, rfl⟩
  · rintro (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩) <;> simp [hA]

theorem sum_strings_succ (m : ℕ) (f : List Bool → ℝ) :
    ∑ J ∈ strings (m + 1), f J = ∑ A ∈ strings m, (f (true :: A) + f (false :: A)) := by
  have hd : Disjoint ((strings m).image (List.cons true)) ((strings m).image (List.cons false)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨B, _, h⟩ := Finset.mem_image.mp hb
    simp at h
  have i1 : Set.InjOn (List.cons true) (strings m : Set (List Bool)) :=
    fun x _ y _ h => (List.cons.inj h).2
  have i2 : Set.InjOn (List.cons false) (strings m : Set (List Bool)) :=
    fun x _ y _ h => (List.cons.inj h).2
  rw [strings_succ, Finset.sum_union hd, Finset.sum_image i1, Finset.sum_image i2,
    ← Finset.sum_add_distrib]

theorem sum_weight (p : ℝ) (m : ℕ) : ∑ A ∈ strings m, weight p A = 1 := by
  induction m with
  | zero =>
    rw [strings_zero, Finset.sum_singleton]
    unfold weight bitNorm
    simp
  | succ m ih =>
    rw [sum_strings_succ, ← ih]
    apply Finset.sum_congr rfl
    intro A _
    rw [weight_cons_true, weight_cons_false]
    ring


/-! ### Degree classes -/

theorem hset_deg (n i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ n) :
    (strings n).filter (fun I => degree I = i) =
      (strings (n - i)).image (fun A => A ++ false :: List.replicate (i - 1) true) := by
  ext I
  simp only [Finset.mem_filter, Finset.mem_image, mem_strings]
  constructor
  · rintro ⟨hl, hd⟩
    have hf : false ∈ I := by
      by_contra hc
      rw [degree_nf I hc] at hd
      omega
    obtain ⟨Q, t, rfl⟩ := decompR I hf
    rw [degreeR] at hd
    refine ⟨Q, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_replicate] at hl
      omega
    · rw [show i - 1 = t by omega]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_replicate]
      omega
    · rw [degreeR]
      omega

theorem sum_deg (p : ℝ) (n i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ n) :
    ∑ I ∈ (strings n).filter (fun I => degree I = i), weight p I = p ^ (i - 1) * (1 - p) := by
  rw [hset_deg n i h1 h2, Finset.sum_image]
  · simp_rw [weight_app]
    rw [← Finset.sum_mul, sum_weight]
    ring
  · intro x _ y _ h
    exact List.append_cancel_right h

open Classical in
theorem hset_child (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hin : i ≤ n) :
    (strings (n + 1)).filter
        (fun J => degree J = j ∧ ∃ I ∈ strings n, degree I = i ∧ Conflict I J) =
      (strings (n - i)).image
        (fun A => A ++ false :: (List.replicate (i - j) true ++ false :: List.replicate (j - 1) true)) := by
  ext J
  simp only [Finset.mem_filter, Finset.mem_image, mem_strings]
  constructor
  · rintro ⟨hl, hd, I, hIl, hId, hc⟩
    have hf : false ∈ I := by
      by_contra hc'
      rw [degree_nf I hc'] at hId
      omega
    obtain ⟨Q, t, rfl⟩ := decompR I hf
    rw [degreeR] at hId
    have hlen : J.length = (Q ++ false :: List.replicate t true).length + 1 := by rw [hl, hIl]
    obtain ⟨Q', a, b, e1, e2⟩ := coreR _ _ hc hlen
    obtain ⟨hQ, ht⟩ := uniqR e1
    rw [e2, deg_child] at hd
    refine ⟨Q, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_replicate] at hIl
      omega
    · rw [e2, ← hQ, show i - j = a by omega, show j - 1 = b by omega]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨?_, ?_, A ++ false :: List.replicate (i - 1) true, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_replicate]
      omega
    · rw [deg_child]
      omega
    · simp only [List.length_append, List.length_cons, List.length_replicate]
      omega
    · rw [degreeR]
      omega
    · have := conflictR A (i - j) (j - 1)
      rw [show i - j + (j - 1) = i - 1 by omega] at this
      exact this

open Classical in
theorem sum_child (p : ℝ) (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hin : i ≤ n) :
    ∑ J ∈ (strings (n + 1)).filter
        (fun J => degree J = j ∧ ∃ I ∈ strings n, degree I = i ∧ Conflict I J), weight p J =
      p ^ (i - 1) * (1 - p) ^ 2 := by
  have hp : p ^ (i - j) * p ^ (j - 1) = p ^ (i - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hset_child n i j hj hji hin, Finset.sum_image]
  · simp_rw [weight_child]
    rw [← Finset.sum_mul, sum_weight, one_mul, ← hp]
    ring
  · intro x _ y _ h
    exact List.append_cancel_right h


end Aux_SecSampling_lemma_12

open Classical in
open SecSampling Aux_SecSampling_lemma_12 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hin : i ≤ n) :
    ∑ I ∈ (strings n).filter (fun I => degree I = i), weight p I = p ^ (i - 1) * (1 - p) ∧
    ∑ J ∈ (strings (n + 1)).filter
        (fun J => degree J = j ∧ ∃ I ∈ strings n, degree I = i ∧ Conflict I J), weight p J =
      (1 - p) * ∑ I ∈ (strings n).filter (fun I => degree I = i), weight p I ∧
    ∑ J ∈ (strings (n + 1)).filter
        (fun J => degree J = j ∧ ∃ I ∈ strings n, degree I = i ∧ Conflict I J), weight p J =
      p ^ (i - 1) * (1 - p) ^ 2 := by
  have h1 : 1 ≤ i := le_trans hj hji
  refine ⟨sum_deg p n i h1 hin, ?_, sum_child p n i j hj hji hin⟩
  rw [sum_child p n i j hj hji hin, sum_deg p n i h1 hin]
  ring

