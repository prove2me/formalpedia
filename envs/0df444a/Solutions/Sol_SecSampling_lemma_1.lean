-- Prove2me | solution 1 for SecSampling.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:32:09.534953+00:00
-- url     : https://prove2.me/submissions/90d73672-3c98-4b22-89e1-34625cdcd6ce

import Mathlib
import Definitions.Def_SecSampling_AOSp
import Definitions.Def_SecSampling_FractionalSelection

namespace Aux_SecSampling_lemma_1

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


/-! ### The k-max strategy on last-zero instances -/

theorem getLast_take (Q : List Bool) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ Q.length) :
    (Q.take j).getLast? = Q[j - 1]? := by
  rw [List.getLast?_eq_getElem?, List.length_take, min_eq_left h2, List.getElem?_take,
    if_pos (by omega)]

theorem prod01 (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∏ j ∈ s, (1 - if c j then (1 : ℝ) else 0) = if ∀ j ∈ s, ¬ c j then 1 else 0 := by
  split_ifs with h
  · apply Finset.prod_eq_one
    intro j hj
    simp only [if_neg (h j hj), sub_zero]
  · push_neg at h
    obtain ⟨j, hj, hc⟩ := h
    apply Finset.prod_eq_zero hj
    simp only [if_pos hc, sub_self]

theorem ite_mul_eq_one (P R : Prop) [Decidable P] [Decidable R] :
    ((if P then (1 : ℝ) else 0) * (if R then 1 else 0) = 1) ↔ P ∧ R := by
  split_ifs with hP hR hR <;> simp_all

theorem bitNorm_R (Q : List Bool) (t : ℕ) :
    bitNorm (Q ++ false :: List.replicate t true) = Q.count true + t := by
  unfold bitNorm
  rw [List.count_append, ct_false_cons, ct_rep]

theorem win_kmax (p : ℝ) (Q : List Bool) (t : ℕ) :
    winLZ (kmaxLZ p) (Q ++ false :: List.replicate t true) = 1 ↔
      (t < kOf p ∧ ∀ j, 1 ≤ j → j ≤ Q.length → Q[j - 1]? = some false →
        kOf p ≤ (Q.count true + t) - (Q.take j).count true) := by
  have hf : false ∈ Q ++ false :: List.replicate t true := by simp
  unfold winLZ stopProbAt
  rw [if_pos hf, bitNorm_R, lzR, tk]
  have e1 : (Q ++ [false]).getLast? = some false := List.getLast?_concat
  have e2 : Q.count true + t - (Q ++ [false]).count true = t := by
    rw [List.count_append]
    simp
  have hlast : kmaxLZ p (Q.count true + t) (Q ++ [false]) = if t < kOf p then 1 else 0 := by
    by_cases ht : t < kOf p
    · rw [if_pos ht]
      simp only [kmaxLZ]
      rw [if_pos ⟨e1, by rw [e2]; exact ht⟩]
    · rw [if_neg ht]
      simp only [kmaxLZ]
      rw [if_neg (fun h => ht (by have h2 := h.2; rw [e2] at h2; exact h2))]
  have hfac : ∀ j ∈ Finset.Ico 1 (Q.length + 1),
      kmaxLZ p (Q.count true + t) ((Q ++ false :: List.replicate t true).take j) =
        if (Q[j - 1]? = some false ∧ Q.count true + t - (Q.take j).count true < kOf p)
          then 1 else 0 := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [List.take_append_of_le_length (l₁ := Q) (l₂ := false :: List.replicate t true) (i := j)
      (by omega)]
    simp only [kmaxLZ]
    rw [getLast_take Q j (by omega) (by omega)]
  have hprod : ∏ j ∈ Finset.Ico 1 (Q.length + 1),
      (1 - kmaxLZ p (Q.count true + t) ((Q ++ false :: List.replicate t true).take j)) =
      ∏ j ∈ Finset.Ico 1 (Q.length + 1),
        (1 - if (Q[j - 1]? = some false ∧ Q.count true + t - (Q.take j).count true < kOf p)
          then (1 : ℝ) else 0) :=
    Finset.prod_congr rfl (fun j hj => by rw [hfac j hj])
  rw [hprod, hlast, prod01 (Finset.Ico 1 (Q.length + 1))
    (fun j => Q[j - 1]? = some false ∧ Q.count true + t - (Q.take j).count true < kOf p),
    ite_mul_eq_one]
  apply and_congr_right
  intro _
  constructor
  · intro h j h1 h2 h3
    by_contra hc
    push_neg at hc
    exact h j (Finset.mem_Ico.mpr ⟨h1, by omega⟩) ⟨h3, hc⟩
  · intro h j hj hc
    rw [Finset.mem_Ico] at hj
    have := h j hj.1 (by omega) hc.1
    have := hc.2
    omega

theorem win_nf (q : LZStrategy) (I : List Bool) (h : false ∉ I) : winLZ q I = 1 := by
  unfold winLZ
  rw [if_neg h]


/-! ### Performance of k-max in the last-zero problem -/

section KPerf

open Classical

theorem kw_cons_true (p : ℝ) (v : List Bool) :
    winLZ (kmaxLZ p) (true :: v) = 1 ↔ winLZ (kmaxLZ p) v = 1 := by
  by_cases hf : false ∈ v
  · obtain ⟨Q, t, rfl⟩ := decompR v hf
    have e : true :: (Q ++ false :: List.replicate t true) =
        (true :: Q) ++ false :: List.replicate t true := by simp
    rw [e, win_kmax, win_kmax]
    apply and_congr_right
    intro _
    rw [List.length_cons, ct_true_cons]
    constructor
    · intro h j h1 h2 h3
      have := h (j + 1) (by omega) (by omega) (by
        rw [Nat.add_sub_cancel]
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [Nat.add_sub_cancel] at h3
        rw [List.getElem?_cons_succ]
        exact h3)
      rw [List.take_succ_cons, ct_true_cons] at this
      omega
    · intro h j h1 h2 h3
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [Nat.add_sub_cancel] at h3
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at h3
        simp at h3
      | succ i =>
        rw [List.getElem?_cons_succ] at h3
        have := h (i + 1) (by omega) (by omega) (by rw [Nat.add_sub_cancel]; exact h3)
        rw [List.take_succ_cons, ct_true_cons]
        omega
  · have hf' : false ∉ true :: v := by simp [hf]
    rw [win_nf _ _ hf, win_nf _ _ hf']

theorem kw_cons_false (p : ℝ) (v : List Bool) :
    winLZ (kmaxLZ p) (false :: v) = 1 ↔
      (false ∉ v ∧ v.length < kOf p) ∨
        (false ∈ v ∧ winLZ (kmaxLZ p) v = 1 ∧ kOf p ≤ v.count true) := by
  by_cases hf : false ∈ v
  · obtain ⟨Q, t, rfl⟩ := decompR v hf
    have e : false :: (Q ++ false :: List.replicate t true) =
        (false :: Q) ++ false :: List.replicate t true := by simp
    have hc : (Q ++ false :: List.replicate t true).count true = Q.count true + t := by
      rw [List.count_append, ct_false_cons, ct_rep]
    rw [e, win_kmax, win_kmax, hc, List.length_cons, ct_false_cons]
    constructor
    · rintro ⟨ht, h⟩
      right
      refine ⟨hf, ⟨ht, ?_⟩, ?_⟩
      · intro j h1 h2 h3
        have := h (j + 1) (by omega) (by omega) (by
          rw [Nat.add_sub_cancel]
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          rw [Nat.add_sub_cancel] at h3
          rw [List.getElem?_cons_succ]
          exact h3)
        rw [List.take_succ_cons, ct_false_cons] at this
        exact this
      · have := h 1 le_rfl (by omega) (by simp)
        have h0 : ((false :: Q).take 1).count true = 0 := by simp
        omega
    · rintro (⟨h, _⟩ | ⟨_, ⟨ht, h⟩, hk⟩)
      · exact absurd hf h
      · refine ⟨ht, ?_⟩
        intro j h1 h2 h3
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [Nat.add_sub_cancel] at h3
        cases i with
        | zero =>
          have h0 : ((false :: Q).take (0 + 1)).count true = 0 := by simp
          omega
        | succ i =>
          rw [List.getElem?_cons_succ] at h3
          have := h (i + 1) (by omega) (by omega) (by rw [Nat.add_sub_cancel]; exact h3)
          rw [List.take_succ_cons, ct_false_cons]
          exact this
  · have hv := nf_rep v hf
    have e : false :: v = [] ++ false :: List.replicate v.length true := by
      rw [List.nil_append, ← hv]
    rw [e, win_kmax]
    constructor
    · rintro ⟨ht, _⟩
      left
      exact ⟨hf, ht⟩
    · rintro (⟨_, ht⟩ | ⟨h, _⟩)
      · refine ⟨ht, ?_⟩
        intro j h1 h2 _
        simp at h2
        omega
      · exact absurd h hf

theorem kw_count (p : ℝ) (v : List Bool) (hf : false ∈ v) (hw : winLZ (kmaxLZ p) v = 1)
    (hl : kOf p + 1 ≤ v.length) : kOf p ≤ v.count true := by
  obtain ⟨Q, t, rfl⟩ := decompR v hf
  rw [win_kmax] at hw
  obtain ⟨ht, hall⟩ := hw
  have hc : (Q ++ false :: List.replicate t true).count true = Q.count true + t := by
    rw [List.count_append, ct_false_cons, ct_rep]
  rw [hc]
  simp only [List.length_append, List.length_cons, List.length_replicate] at hl
  by_cases hz : false ∈ Q
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
    have hil : i < Q.length := by
      by_contra hc'
      push_neg at hc'
      rw [List.getElem?_eq_none hc'] at hi
      exact absurd hi (by simp)
    have := hall (i + 1) (by omega) (by omega) (by rw [Nat.add_sub_cancel]; exact hi)
    omega
  · have := ct_of_nf Q hz
    omega

noncomputable def kind (p : ℝ) (v : List Bool) : ℝ := if winLZ (kmaxLZ p) v = 1 then 1 else 0

noncomputable def kperf (p : ℝ) (s : ℕ) : ℝ := ∑ v ∈ strings s, weight p v * kind p v

theorem kperf_succ (p : ℝ) (s : ℕ) :
    kperf p (s + 1) = p * kperf p s + (1 - p) * ∑ v ∈ strings s, weight p v * kind p (false :: v) := by
  unfold kperf
  rw [sum_strings_succ, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro v _
    unfold kind
    rw [weight_cons_true]
    by_cases h : winLZ (kmaxLZ p) v = 1
    · rw [if_pos ((kw_cons_true p v).mpr h), if_pos h]
      ring
    · rw [if_neg (fun h' => h ((kw_cons_true p v).mp h')), if_neg h]
      ring
  · apply Finset.sum_congr rfl
    intro v _
    rw [weight_cons_false]
    ring

theorem rep_mem (s : ℕ) : List.replicate s true ∈ strings s := by
  rw [mem_strings, List.length_replicate]

theorem weight_rep (p : ℝ) (s : ℕ) : weight p (List.replicate s true) = p ^ s := by
  rw [weight_eq, ct_rep, cf_rep, pow_zero, mul_one]

theorem kind_false_small (p : ℝ) (s : ℕ) (hs : s < kOf p) (v : List Bool) (hv : v ∈ strings s) :
    kind p (false :: v) = if v = List.replicate s true then 1 else 0 := by
  rw [mem_strings] at hv
  unfold kind
  by_cases hf : false ∈ v
  · have hne : v ≠ List.replicate s true := by
      intro h
      rw [h] at hf
      exact nf_replicate s hf
    rw [if_neg hne, if_neg]
    rw [kw_cons_false]
    rintro (⟨h, _⟩ | ⟨_, _, hk⟩)
    · exact h hf
    · have h1 := ct_add_cf v
      have h2 : 0 < v.count false := List.count_pos_iff.mpr hf
      omega
  · have he : v = List.replicate s true := by rw [nf_rep v hf, hv]
    rw [if_pos he, if_pos]
    rw [kw_cons_false]
    left
    exact ⟨hf, by omega⟩

theorem kind_false_k (p : ℝ) (v : List Bool) (hv : v ∈ strings (kOf p)) :
    kind p (false :: v) = 0 := by
  rw [mem_strings] at hv
  unfold kind
  rw [if_neg]
  rw [kw_cons_false]
  rintro (⟨_, h⟩ | ⟨hf, _, hk⟩)
  · omega
  · have h1 := ct_add_cf v
    have h2 : 0 < v.count false := List.count_pos_iff.mpr hf
    omega

theorem kind_false_big (p : ℝ) (s : ℕ) (hs : kOf p + 1 ≤ s) (v : List Bool) (hv : v ∈ strings s) :
    kind p (false :: v) = kind p v - if v = List.replicate s true then 1 else 0 := by
  rw [mem_strings] at hv
  unfold kind
  by_cases hf : false ∈ v
  · have hne : v ≠ List.replicate s true := by
      intro h
      rw [h] at hf
      exact nf_replicate s hf
    rw [if_neg hne, sub_zero]
    by_cases hw : winLZ (kmaxLZ p) v = 1
    · rw [if_pos hw, if_pos]
      rw [kw_cons_false]
      right
      exact ⟨hf, hw, kw_count p v hf hw (by omega)⟩
    · rw [if_neg hw, if_neg]
      rw [kw_cons_false]
      rintro (⟨h, _⟩ | ⟨_, h, _⟩)
      · exact h hf
      · exact hw h
  · have he : v = List.replicate s true := by rw [nf_rep v hf, hv]
    rw [if_pos he, if_pos (win_nf _ v hf), if_neg]
    · ring
    rw [kw_cons_false]
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · omega
    · exact hf h

theorem kperf_zero (p : ℝ) : kperf p 0 = 1 := by
  unfold kperf
  rw [strings_zero, Finset.sum_singleton]
  unfold kind
  rw [if_pos (win_nf _ [] (by simp))]
  unfold weight bitNorm
  simp

theorem kperf_small (p : ℝ) : ∀ s, s ≤ kOf p →
    p * kperf p s = p ^ (s + 1) + s * (1 - p) * p ^ s := by
  intro s
  induction s with
  | zero =>
    intro _
    rw [kperf_zero]
    simp
  | succ s ih =>
    intro hs
    rw [kperf_succ]
    have hsum0 : ∑ v ∈ strings s, weight p v * kind p (false :: v) =
        ∑ v ∈ strings s, if v = List.replicate s true then weight p v else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [kind_false_small p s (by omega) v hv]
      split_ifs <;> ring
    have hsum : ∑ v ∈ strings s, weight p v * kind p (false :: v) = p ^ s := by
      rw [hsum0, Finset.sum_ite_eq' (strings s) (List.replicate s true), if_pos (rep_mem s),
        weight_rep]
    rw [hsum]
    have := ih (by omega)
    push_cast
    linear_combination p * this

theorem kperf_big (p : ℝ) : ∀ j, kperf p (kOf p + 1 + j) = guarantee p + p ^ (kOf p + 1 + j) := by
  intro j
  induction j with
  | zero =>
    rw [Nat.add_zero, kperf_succ]
    have hsum : ∑ v ∈ strings (kOf p), weight p v * kind p (false :: v) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [kind_false_k p v hv, mul_zero]
    rw [hsum, mul_zero, add_zero]
    have := kperf_small p (kOf p) le_rfl
    rw [this]
    unfold guarantee
    ring
  | succ j ih =>
    have e : kOf p + 1 + (j + 1) = (kOf p + 1 + j) + 1 := by ring
    rw [e, kperf_succ]
    have hsum0 : ∑ v ∈ strings (kOf p + 1 + j), weight p v * kind p (false :: v) =
        ∑ v ∈ strings (kOf p + 1 + j), (weight p v * kind p v -
          if v = List.replicate (kOf p + 1 + j) true then weight p v else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [kind_false_big p (kOf p + 1 + j) (by omega) v hv]
      split_ifs <;> ring
    have hsum : ∑ v ∈ strings (kOf p + 1 + j), weight p v * kind p (false :: v) =
        kperf p (kOf p + 1 + j) - p ^ (kOf p + 1 + j) := by
      unfold kperf
      rw [hsum0, Finset.sum_sub_distrib, Finset.sum_ite_eq' _ (List.replicate (kOf p + 1 + j) true),
        if_pos (rep_mem _), weight_rep]
    rw [hsum, ih]
    ring

end KPerf


/-! ### k-max in the AOSp model -/

section AOSpSec

theorem hist_last {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) (seen : List (Fin n)) (x : Fin n) :
    (hist v S (seen ++ [x])).getLast? = some (rankPair v S seen x) := by
  unfold hist
  rw [List.getLast?_eq_getElem?, List.getElem?_ofFn, dif_pos]
  · congr 1
    congr 1 <;> simp
  · simp

theorem kmax_hist {n : ℕ} (p : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (seen : List (Fin n))
    (x : Fin n) (m : ℕ) :
    kmax p n m (hist v S (seen ++ [x])) =
      if (S.filter (fun y => v x < v y)).card < kOf p then 1 else 0 := by
  simp only [kmax]
  rw [hist_last]
  rfl

def elg {n : ℕ} (p : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (x : Fin n) : Prop :=
  (S.filter (fun y => v x < v y)).card < kOf p

open Classical in
noncomputable def Fk {n : ℕ} (v : Fin n → ℝ) (L : List (Fin n)) (el : Fin n → Prop) :
    List (Fin n) → ℝ
  | [] => 0
  | x :: r => if el x then (if ∀ y ∈ L, v y ≤ v x then 1 else 0) else Fk v L el r

theorem Fk_nil {n : ℕ} (v : Fin n → ℝ) (L : List (Fin n)) (el : Fin n → Prop) : Fk v L el [] = 0 := by
  rw [Fk]

theorem Fk_cons_el {n : ℕ} (v : Fin n → ℝ) (L : List (Fin n)) (el : Fin n → Prop) (x : Fin n)
    (r : List (Fin n)) (h : el x) :
    Fk v L el (x :: r) = if ∀ y ∈ L, v y ≤ v x then 1 else 0 := by
  rw [Fk, if_pos h]

theorem Fk_cons_nel {n : ℕ} (v : Fin n → ℝ) (L : List (Fin n)) (el : Fin n → Prop) (x : Fin n)
    (r : List (Fin n)) (h : ¬ el x) : Fk v L el (x :: r) = Fk v L el r := by
  rw [Fk, if_neg h]

theorem stop_kmax {n : ℕ} (p : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (L : List (Fin n)) :
    ∀ (rest seen : List (Fin n)), stopAtMaxProb (kmax p) v S L seen rest =
      Fk v L (elg p v S) rest := by
  intro rest
  induction rest with
  | nil =>
    intro seen
    rfl
  | cons x r ih =>
    intro seen
    rw [stopAtMaxProb, kmax_hist, ih]
    by_cases hel : elg p v S x
    · rw [Fk_cons_el v L (elg p v S) x r hel]
      have hel' : (S.filter (fun y => v x < v y)).card < kOf p := hel
      rw [if_pos hel']
      split_ifs <;> ring
    · rw [Fk_cons_nel v L (elg p v S) x r hel]
      have hel' : ¬ (S.filter (fun y => v x < v y)).card < kOf p := hel
      rw [if_neg hel']
      split_ifs <;> ring

theorem Fk_01 {n : ℕ} (v : Fin n → ℝ) (L : List (Fin n)) (el : Fin n → Prop) :
    ∀ rest, Fk v L el rest = 0 ∨ Fk v L el rest = 1 := by
  intro rest
  induction rest with
  | nil => left; rfl
  | cons x r ih =>
    classical
    by_cases h : el x
    · rw [Fk_cons_el v L el x r h]
      split_ifs
      · right; rfl
      · left; rfl
    · rw [Fk_cons_nel v L el x r h]
      exact ih

theorem Fk_congr {n : ℕ} (v : Fin n → ℝ) (L L' : List (Fin n)) (el : Fin n → Prop) :
    ∀ rest, (∀ z ∈ rest, ((∀ y ∈ L, v y ≤ v z) ↔ (∀ y ∈ L', v y ≤ v z))) →
      Fk v L el rest = Fk v L' el rest := by
  intro rest
  induction rest with
  | nil => intro _; rfl
  | cons x r ih =>
    intro h
    classical
    by_cases hx : el x
    · rw [Fk_cons_el v L el x r hx, Fk_cons_el v L' el x r hx]
      have hh := h x (by simp)
      by_cases hm : ∀ y ∈ L, v y ≤ v x
      · rw [if_pos hm, if_pos (hh.mp hm)]
      · rw [if_neg hm, if_neg (fun h' => hm (hh.mpr h'))]
    · rw [Fk_cons_nel v L el x r hx, Fk_cons_nel v L' el x r hx]
      exact ih (fun z hz => h z (by simp [hz]))

theorem Fk_of_C {n : ℕ} (v : Fin n → ℝ) (L : List (Fin n)) (el : Fin n → Prop) :
    ∀ rest, (∃ M ∈ rest, el M ∧ (∀ y ∈ L, v y ≤ v M) ∧ ∀ y ∈ rest, y ≠ M → ¬ el y) →
      Fk v L el rest = 1 := by
  intro rest
  induction rest with
  | nil =>
    rintro ⟨M, hM, _⟩
    simp at hM
  | cons x r ih =>
    rintro ⟨M, hM, h1, h2, h3⟩
    classical
    by_cases hxM : x = M
    · rw [hxM, Fk_cons_el v L el M r h1, if_pos h2]
    · rw [Fk_cons_nel v L el x r (h3 x (by simp) hxM)]
      apply ih
      rcases List.mem_cons.mp hM with h | h
      · exact absurd h.symm hxM
      · exact ⟨M, h, h1, h2, fun y hy hne => h3 y (by simp [hy]) hne⟩

theorem C_of_Fk {n : ℕ} (v : Fin n → ℝ) (L : List (Fin n)) (el : Fin n → Prop) :
    ∀ rest, rest.Pairwise (fun x y => v x < v y) → (∀ z ∈ rest, z ∈ L) → Fk v L el rest = 1 →
      ∃ M ∈ rest, el M ∧ (∀ y ∈ L, v y ≤ v M) ∧ ∀ y ∈ rest, y ≠ M → ¬ el y := by
  intro rest
  induction rest with
  | nil =>
    intro _ _ h
    rw [Fk_nil] at h
    norm_num at h
  | cons x r ih =>
    intro hp hsub h
    classical
    rw [List.pairwise_cons] at hp
    by_cases hx : el x
    · rw [Fk_cons_el v L el x r hx] at h
      by_cases hm : ∀ y ∈ L, v y ≤ v x
      · refine ⟨x, by simp, hx, hm, ?_⟩
        intro y hy hne
        rcases List.mem_cons.mp hy with h' | h'
        · exact absurd h' hne
        · have h1 := hp.1 y h'
          have h2 := hm y (hsub y (by simp [h']))
          exfalso
          linarith
      · rw [if_neg hm] at h
        norm_num at h
    · rw [Fk_cons_nel v L el x r hx] at h
      obtain ⟨M, hM, h1, h2, h3⟩ := ih hp.2 (fun z hz => hsub z (by simp [hz])) h
      refine ⟨M, by simp [hM], h1, h2, ?_⟩
      intro y hy hne
      rcases List.mem_cons.mp hy with h' | h'
      · rw [h']
        exact hx
      · exact h3 y h' hne

noncomputable def Wl {n : ℕ} (p : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (L : List (Fin n)) : ℝ :=
  winOnSample (kmax p) v S L

theorem Wl_eq {n : ℕ} (p : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (L : List (Fin n)) (hL : L ≠ []) :
    Wl p v S L = Fk v L (elg p v S) L := by
  unfold Wl winOnSample
  rw [if_neg hL, stop_kmax]

theorem count_filter_mem {n : ℕ} (S : Finset (Fin n)) (T : List (Fin n)) :
    (T.map (fun x => decide (x ∈ S))).count true = (T.filter (fun x => decide (x ∈ S))).length := by
  induction T with
  | nil => rfl
  | cons a T ih =>
    by_cases h : a ∈ S
    · simp [h, ih]
    · simp [h, ih]

theorem upper_count {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) (x : Fin n) (T : List (Fin n))
    (hp : (x :: T).Pairwise (fun a b => v a < v b))
    (hup : ∀ z ∈ x :: T, ∀ y, v z < v y → y ∈ x :: T) :
    (T.map (fun y => decide (y ∈ S))).count true = (S.filter (fun y => v x < v y)).card := by
  rw [count_filter_mem]
  rw [List.pairwise_cons] at hp
  have hnd : T.Nodup := hp.2.imp (fun h => ne_of_apply_ne v (ne_of_lt h))
  have hnd2 : (T.filter (fun y => decide (y ∈ S))).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hnd2]
  congr 1
  ext y
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, hp.1 y h1⟩
  · rintro ⟨h1, h2⟩
    have := hup x (by simp) y h2
    rcases List.mem_cons.mp this with h | h
    · rw [h] at h2
      exact absurd h2 (lt_irrefl _)
    · exact ⟨h, h1⟩

theorem key_induct {n : ℕ} (p : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) :
    ∀ T : List (Fin n), T.Pairwise (fun a b => v a < v b) →
      (∀ z ∈ T, ∀ y, v z < v y → y ∈ T) →
      Wl p v S (T.filter (fun x => decide (x ∉ S))) = kind p (T.map (fun x => decide (x ∈ S))) := by
  intro T
  induction T with
  | nil =>
    intro _ _
    unfold Wl winOnSample kind
    rw [if_pos List.filter_nil, List.map_nil, if_pos (win_nf _ [] (by simp))]
  | cons x T ih =>
    intro hp hup
    have hp' := hp
    rw [List.pairwise_cons] at hp'
    have hupT : ∀ z ∈ T, ∀ y, v z < v y → y ∈ T := by
      intro z hz y hy
      have := hup z (by simp [hz]) y hy
      rcases List.mem_cons.mp this with h | h
      · rw [h] at hy
        have := hp'.1 z hz
        exfalso
        linarith
      · exact h
    have ihT := ih hp'.2 hupT
    have hcount := upper_count v S x T hp hup
    by_cases hxS : x ∈ S
    · have e1 : (x :: T).filter (fun x => decide (x ∉ S)) = T.filter (fun x => decide (x ∉ S)) := by
        simp [hxS]
      have e2 : (x :: T).map (fun x => decide (x ∈ S)) = true :: T.map (fun x => decide (x ∈ S)) := by
        simp [hxS]
      rw [e1, e2, ihT]
      unfold kind
      by_cases hw : winLZ (kmaxLZ p) (T.map (fun x => decide (x ∈ S))) = 1
      · rw [if_pos hw, if_pos ((kw_cons_true p _).mpr hw)]
      · rw [if_neg hw, if_neg (fun h => hw ((kw_cons_true p _).mp h))]
    · have e1 : (x :: T).filter (fun x => decide (x ∉ S)) = x :: T.filter (fun x => decide (x ∉ S)) := by
        simp [hxS]
      have e2 : (x :: T).map (fun x => decide (x ∈ S)) = false :: T.map (fun x => decide (x ∈ S)) := by
        simp [hxS]
      rw [e1, e2]
      obtain ⟨L', hL'⟩ : ∃ L', L' = T.filter (fun x => decide (x ∉ S)) := ⟨_, rfl⟩
      obtain ⟨I', hI'⟩ : ∃ I', I' = T.map (fun x => decide (x ∈ S)) := ⟨_, rfl⟩
      rw [← hL', ← hI']
      rw [← hL', ← hI'] at ihT
      rw [← hI'] at hcount
      have hfI : false ∈ I' ↔ L' ≠ [] := by
        rw [hI', hL']
        constructor
        · intro h
          obtain ⟨y, hy, hy2⟩ := List.mem_map.mp h
          intro h0
          have : y ∈ T.filter (fun x => decide (x ∉ S)) := by
            rw [List.mem_filter]
            refine ⟨hy, ?_⟩
            simpa using hy2
          rw [h0] at this
          simp at this
        · intro h
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ h
          rw [List.mem_filter] at hy
          apply List.mem_map.mpr
          refine ⟨y, hy.1, ?_⟩
          simpa using hy.2
      have hlen : I'.length = T.length := by rw [hI', List.length_map]
      unfold Wl winOnSample
      rw [if_neg (List.cons_ne_nil _ _), stop_kmax]
      unfold kind
      by_cases hL0 : L' = []
      · -- only x is online
        have hnf : false ∉ I' := fun h => (hfI.mp h) hL0
        have hct : I'.count true = I'.length := ct_of_nf I' hnf
        rw [hL0]
        by_cases hel : elg p v S x
        · have hel' := hel
          unfold elg at hel'
          rw [Fk_cons_el v [x] (elg p v S) x [] hel, if_pos (show ∀ y ∈ [x], v y ≤ v x by simp)]
          rw [if_pos]
          rw [kw_cons_false]
          left
          exact ⟨hnf, by omega⟩
        · have hel' := hel
          unfold elg at hel'
          rw [Fk_cons_nel v [x] (elg p v S) x [] hel, Fk_nil]
          rw [if_neg]
          rw [kw_cons_false]
          rintro (⟨_, h⟩ | ⟨h, _⟩)
          · omega
          · exact hnf h
      · have hfx : false ∈ I' := hfI.mpr hL0
        obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hL0
        have hyT : y ∈ T := by
          rw [hL', List.mem_filter] at hy
          exact hy.1
        have hxy : v x < v y := hp'.1 y hyT
        have hnm : ¬ ∀ z ∈ x :: L', v z ≤ v x := by
          intro h
          have := h y (by simp [hy])
          linarith
        have hcong : Fk v (x :: L') (elg p v S) L' =
            Fk v L' (elg p v S) L' := by
          apply Fk_congr
          intro z hz
          have hzT : z ∈ T := by
            rw [hL', List.mem_filter] at hz
            exact hz.1
          have hxz : v x < v z := hp'.1 z hzT
          constructor
          · intro h w hw
            exact h w (by simp [hw])
          · intro h w hw
            rcases List.mem_cons.mp hw with h' | h'
            · rw [h']
              linarith
            · exact h w h'
        have hW' : Wl p v S L' =
            Fk v L' (elg p v S) L' := Wl_eq p v S L' hL0
        by_cases hel : elg p v S x
        · have hel' := hel
          unfold elg at hel'
          rw [Fk_cons_el v (x :: L') (elg p v S) x L' hel, if_neg hnm]
          rw [if_neg]
          rw [kw_cons_false]
          rintro (⟨h, _⟩ | ⟨_, _, hk⟩)
          · exact h hfx
          · omega
        · have hel' := hel
          unfold elg at hel'
          rw [Fk_cons_nel v (x :: L') (elg p v S) x L' hel, hcong, ← hW', ihT]
          unfold kind
          by_cases hw : winLZ (kmaxLZ p) I' = 1
          · rw [if_pos hw, if_pos]
            rw [kw_cons_false]
            right
            exact ⟨hfx, hw, by omega⟩
          · rw [if_neg hw, if_neg]
            rw [kw_cons_false]
            rintro (⟨h, _⟩ | ⟨_, h, _⟩)
            · exact h hfx
            · exact hw h

end AOSpSec


section L1

theorem kperf_val' (p : ℝ) (s : ℕ) (hs : kOf p + 1 ≤ s) : kperf p s = guarantee p + p ^ s := by
  obtain ⟨j, rfl⟩ : ∃ j, s = kOf p + 1 + j := ⟨s - (kOf p + 1), by omega⟩
  exact kperf_big p j

theorem kperf_ge (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : n ≤ kOf p) :
    guarantee p ≤ kperf p n := by
  have hk := kperf_small p n hn
  have hmono : ∀ d j, j + d = kOf p →
      p ^ (kOf p + 1) + (kOf p : ℝ) * (1 - p) * p ^ (kOf p) ≤ p ^ (j + 1) + (j : ℝ) * (1 - p) * p ^ j := by
    intro d
    induction d with
    | zero =>
      intro j hj
      obtain rfl : j = kOf p := by omega
      exact le_refl _
    | succ d ih =>
      intro j hj
      have h1 := ih (j + 1) (by omega)
      have e : p ^ (j + 1) + (j : ℝ) * (1 - p) * p ^ j -
          (p ^ (j + 1 + 1) + ((j : ℝ) + 1) * (1 - p) * p ^ (j + 1)) = (1 - p) ^ 2 * j * p ^ j := by
        ring
      have h2 : 0 ≤ (1 - p) ^ 2 * (j : ℝ) * p ^ j :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg j)) (pow_nonneg hp0.le j)
      push_cast at h1
      linarith
  have h3 := hmono (kOf p - n) n (by omega)
  have h4 : p * guarantee p ≤ p ^ (kOf p + 1) + (kOf p : ℝ) * (1 - p) * p ^ (kOf p) := by
    unfold guarantee
    have e : p ^ (kOf p + 1) + (kOf p : ℝ) * (1 - p) * p ^ (kOf p) -
        p * ((kOf p : ℝ) * p ^ (kOf p) * (1 - p)) =
        p ^ (kOf p + 1) + (kOf p : ℝ) * (1 - p) ^ 2 * p ^ (kOf p) := by ring
    have h5 : 0 ≤ p ^ (kOf p + 1) := pow_nonneg hp0.le _
    have h6 : 0 ≤ (kOf p : ℝ) * (1 - p) ^ 2 * p ^ (kOf p) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (pow_nonneg hp0.le _)
    linarith
  have h7 : p * guarantee p ≤ p * kperf p n := by linarith
  exact le_of_mul_le_mul_left h7 hp0

theorem count_ofFn_map {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    ((List.ofFn σ).map (fun x => decide (x ∈ S))).count true = S.card := by
  rw [count_filter_mem]
  have hnd : (List.ofFn σ).Nodup := List.nodup_ofFn.mpr σ.injective
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨List.mem_ofFn.mpr ⟨σ.symm x, by simp⟩, h⟩

theorem weight_Phi {n : ℕ} (p : ℝ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    weight p ((List.ofFn σ).map (fun x => decide (x ∈ S))) = sampleWeight p S := by
  rw [weight_eq]
  unfold sampleWeight
  have h1 := count_ofFn_map σ S
  have h2 := ct_add_cf ((List.ofFn σ).map (fun x => decide (x ∈ S)))
  rw [List.length_map, List.length_ofFn] at h2
  have h3 : ((List.ofFn σ).map (fun x => decide (x ∈ S))).count false = n - S.card := by omega
  rw [h1, h3]

theorem sum_Phi {n : ℕ} (p : ℝ) (σ : Equiv.Perm (Fin n)) :
    ∑ S : Finset (Fin n), sampleWeight p S * kind p ((List.ofFn σ).map (fun x => decide (x ∈ S))) =
      kperf p n := by
  unfold kperf
  apply Finset.sum_nbij' (fun S => (List.ofFn σ).map (fun x => decide (x ∈ S)))
    (fun I => Finset.univ.filter (fun x => I[(σ.symm x : ℕ)]? = some true))
  · intro S _
    rw [mem_strings, List.length_map, List.length_ofFn]
  · intro I _
    exact Finset.mem_univ _
  · intro S _
    ext x
    simp [List.getElem?_map, List.getElem?_ofFn]
  · intro I hI
    rw [mem_strings] at hI
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_map, List.getElem?_ofFn]
    by_cases hk : k < n
    · rw [dif_pos hk]
      have hk' : k < I.length := by omega
      simp [Finset.mem_filter, List.getElem?_eq_getElem hk']
    · rw [dif_neg hk]
      simp [List.getElem?_eq_none (l := I) (i := k) (by omega)]
  · intro S _
    rw [weight_Phi]

theorem win_ge {n : ℕ} (p : ℝ) (v : Fin n → ℝ) (hv : Function.Injective v)
    (ord : Finset (Fin n) → List (Fin n)) (hord : IsOnlineOrder ord) (S : Finset (Fin n)) :
    kind p ((List.ofFn (Tuple.sort v)).map (fun x => decide (x ∈ S))) ≤
        winOnSample (kmax p) v S (ord S) ∧
      ((ord S).Pairwise (fun x y => v x < v y) →
        winOnSample (kmax p) v S (ord S) =
          kind p ((List.ofFn (Tuple.sort v)).map (fun x => decide (x ∈ S)))) := by
  have hσ : StrictMono (v ∘ Tuple.sort v) :=
    (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
  have hps : (List.ofFn (Tuple.sort v)).Pairwise (fun a b => v a < v b) :=
    List.pairwise_ofFn.mpr (fun i j hij => hσ hij)
  have hall : ∀ x, x ∈ List.ofFn (Tuple.sort v) :=
    fun x => List.mem_ofFn.mpr ⟨(Tuple.sort v).symm x, by simp⟩
  have key := key_induct p v S (List.ofFn (Tuple.sort v)) hps (fun _ _ y _ => hall y)
  rw [← key]
  obtain ⟨Lon, hLon⟩ : ∃ L, L = (List.ofFn (Tuple.sort v)).filter (fun x => decide (x ∉ S)) :=
    ⟨_, rfl⟩
  rw [← hLon]
  have hmem : ∀ x, x ∈ ord S ↔ x ∈ Lon := by
    intro x
    rw [(hord S).2 x, hLon, List.mem_filter]
    simp [hall x]
  have hLp : Lon.Pairwise (fun a b => v a < v b) := by
    rw [hLon]
    exact hps.filter _
  by_cases hL0 : Lon = []
  · have hord0 : ord S = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro a ha
      rw [hmem, hL0] at ha
      simp at ha
    unfold Wl winOnSample
    rw [hL0, hord0, if_pos rfl]
    exact ⟨le_refl _, fun _ => rfl⟩
  · have hord0 : ord S ≠ [] := by
      intro h
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hL0
      rw [← hmem, h] at hy
      simp at hy
    have hW1 := Wl_eq p v S Lon hL0
    have hW2 := Wl_eq p v S (ord S) hord0
    have hwo : winOnSample (kmax p) v S (ord S) = Wl p v S (ord S) := rfl
    rw [hwo, hW1, hW2]
    have hC : ∀ L L' : List (Fin n), (∀ x, x ∈ L ↔ x ∈ L') →
        (∃ M ∈ L, elg p v S M ∧ (∀ y ∈ L, v y ≤ v M) ∧ ∀ y ∈ L, y ≠ M → ¬ elg p v S y) →
        (∃ M ∈ L', elg p v S M ∧ (∀ y ∈ L', v y ≤ v M) ∧ ∀ y ∈ L', y ≠ M → ¬ elg p v S y) := by
      intro L L' h ⟨M, hM, h1, h2, h3⟩
      refine ⟨M, (h M).mp hM, h1, fun y hy => h2 y ((h y).mpr hy), fun y hy hne => h3 y ((h y).mpr hy) hne⟩
    constructor
    · rcases Fk_01 v Lon (elg p v S) Lon with h0 | h1
      · rw [h0]
        rcases Fk_01 v (ord S) (elg p v S) (ord S) with h | h
        · linarith
        · linarith
      · rw [h1]
        have hCL := C_of_Fk v Lon (elg p v S) Lon hLp (fun z hz => hz) h1
        have hCo := hC Lon (ord S) (fun x => (hmem x).symm) hCL
        have := Fk_of_C v (ord S) (elg p v S) (ord S) hCo
        linarith
    · intro hop
      rcases Fk_01 v (ord S) (elg p v S) (ord S) with h0 | h1
      · rw [h0]
        rcases Fk_01 v Lon (elg p v S) Lon with h | h
        · rw [h]
        · exfalso
          have hCL := C_of_Fk v Lon (elg p v S) Lon hLp (fun z hz => hz) h
          have hCo := hC Lon (ord S) (fun x => (hmem x).symm) hCL
          rw [Fk_of_C v (ord S) (elg p v S) (ord S) hCo] at h0
          norm_num at h0
      · rw [h1]
        have hCo := C_of_Fk v (ord S) (elg p v S) (ord S) hop (fun z hz => hz) h1
        have hCL := hC (ord S) Lon hmem hCo
        rw [Fk_of_C v Lon (elg p v S) Lon hCL]

theorem sw_nonneg {n : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (S : Finset (Fin n)) :
    0 ≤ sampleWeight p S := by
  unfold sampleWeight
  exact mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)

theorem winProb_ge {n : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (v : Fin n → ℝ)
    (hv : Function.Injective v) (ord : Finset (Fin n) → List (Fin n)) (hord : IsOnlineOrder ord) :
    kperf p n ≤ winProb p (kmax p) v ord := by
  rw [← sum_Phi p (Tuple.sort v)]
  unfold winProb
  apply Finset.sum_le_sum
  intro S _
  exact mul_le_mul_of_nonneg_left (win_ge p v hv ord hord S).1 (sw_nonneg p hp0 hp1 S)

theorem winProb_eq {n : ℕ} (p : ℝ) (v : Fin n → ℝ)
    (hv : Function.Injective v) (ord : Finset (Fin n) → List (Fin n)) (hord : IsOnlineOrder ord)
    (hinc : ∀ S : Finset (Fin n), (ord S).Pairwise (fun x y => v x < v y)) :
    winProb p (kmax p) v ord = kperf p n := by
  rw [← sum_Phi p (Tuple.sort v)]
  unfold winProb
  apply Finset.sum_congr rfl
  intro S _
  rw [(win_ge p v hv ord hord S).2 (hinc S)]

end L1

end Aux_SecSampling_lemma_1

open SecSampling Aux_SecSampling_lemma_1 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ n : ℕ, n ≤ kOf p → ∀ v : Fin n → ℝ, Function.Injective v →
      ∀ ord : Finset (Fin n) → List (Fin n), IsOnlineOrder ord →
        guarantee p ≤ winProb p (kmax p) v ord) ∧
    (∀ n : ℕ, kOf p + 1 ≤ n → ∀ v : Fin n → ℝ, Function.Injective v →
      (∀ ord : Finset (Fin n) → List (Fin n), IsOnlineOrder ord →
        guarantee p + p ^ n ≤ winProb p (kmax p) v ord) ∧
      (∀ ord : Finset (Fin n) → List (Fin n), IsOnlineOrder ord →
        (∀ S : Finset (Fin n), (ord S).Pairwise (fun x y => v x < v y)) →
        winProb p (kmax p) v ord = guarantee p + p ^ n)) := by
  constructor
  · intro n hn v hv ord hord
    exact le_trans (kperf_ge p hp0 hp1 n hn) (winProb_ge p hp0 hp1 v hv ord hord)
  · intro n hn v hv
    constructor
    · intro ord hord
      rw [← kperf_val' p n hn]
      exact winProb_ge p hp0 hp1 v hv ord hord
    · intro ord hord hinc
      rw [winProb_eq p v hv ord hord hinc, kperf_val' p n hn]

