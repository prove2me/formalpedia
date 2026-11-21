-- Prove2me | solution 1 for SecSampling.removed_fraction_adds_up
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:33:18.010057+00:00
-- url     : https://prove2.me/submissions/78b33203-8d74-4acf-a7dd-35804a2553d9

import Mathlib
import Definitions.Def_SecSampling_FractionalSelection

namespace Aux_SecSampling_removed_fraction_adds_up

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

theorem lt_idxOf_ne {α : Type} [BEq α] [LawfulBEq α] (b : α) :
    ∀ (l : List α) (j : ℕ), j < l.idxOf b → l[j]? ≠ some b
  | [], j, h => by simp at h
  | x :: xs, 0, h => by
    rw [List.idxOf_cons] at h
    cases hx : (x == b)
    · have hxb : x ≠ b := by
        intro e; rw [e] at hx; simp at hx
      simpa using hxb
    · rw [hx] at h; simp at h
  | x :: xs, j + 1, h => by
    rw [List.idxOf_cons] at h
    cases hx : (x == b)
    · rw [hx] at h
      have h' : j < xs.idxOf b := by simp at h; omega
      simpa using lt_idxOf_ne b xs j h'
    · rw [hx] at h; simp at h

theorem lz_spec (I : List Bool) (h : false ∈ I) :
    0 < lastZero I ∧ lastZero I ≤ I.length ∧ I[lastZero I - 1]? = some false ∧
      ∀ i, lastZero I ≤ i → i < I.length → I[i]? = some true := by
  have hr : false ∈ I.reverse := List.mem_reverse.mpr h
  have hk : I.reverse.idxOf false < I.reverse.length := List.idxOf_lt_length_iff.mpr hr
  have hlen : I.reverse.length = I.length := List.length_reverse
  have hlz : lastZero I = I.length - I.reverse.idxOf false := by
    unfold lastZero; rw [if_pos h]
  have hget : I.reverse[I.reverse.idxOf false]? = some false := by
    rw [List.getElem?_eq_getElem hk, List.getElem_idxOf hk]
  obtain ⟨k, hkdef⟩ : ∃ k, k = I.reverse.idxOf false := ⟨_, rfl⟩
  rw [← hkdef] at hget hk hlz
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hlz]
    have e : I.length - k - 1 = I.length - 1 - k := by omega
    rw [e, ← List.getElem?_reverse (l := I) (i := k) (by omega)]
    exact hget
  · intro i hi1 hi2
    have hne := lt_idxOf_ne false I.reverse (I.length - 1 - i) (by omega)
    rw [List.getElem?_reverse (l := I) (i := I.length - 1 - i) (by omega)] at hne
    have e : I.length - 1 - (I.length - 1 - i) = i := by omega
    rw [e, List.getElem?_eq_getElem hi2] at hne
    rw [List.getElem?_eq_getElem hi2]
    cases hb : I[i]
    · rw [hb] at hne; exact absurd rfl hne
    · rfl

theorem take_eq_iff {I J : List Bool} {a : ℕ} :
    I.take a = J.take a ↔ ∀ i, i < a → I[i]? = J[i]? := by
  constructor
  · intro h i hi
    have := congrArg (fun L : List Bool => L[i]?) h
    simpa [List.getElem?_take, hi] using this
  · intro h
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take, List.getElem?_take]
    split_ifs with hi
    · exact h i hi
    · rfl

theorem count_drop (I : List Bool) (a : ℕ)
    (h : ∀ i, a ≤ i → i < I.length → I[i]? = some true) :
    (I.drop a).count true = I.length - a := by
  rw [← List.length_drop]
  apply List.count_eq_length.mpr
  intro b hb
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  rw [List.getElem?_drop] at hj
  have hlt : a + j < I.length := by
    by_contra hc
    push_neg at hc
    rw [List.getElem?_eq_none hc] at hj
    exact absurd hj (by simp)
  rw [h (a + j) (by omega) hlt] at hj
  exact Option.some.inj hj

theorem count_split (I : List Bool) (a : ℕ) :
    I.count true = (I.take a).count true + (I.drop a).count true := by
  conv_lhs => rw [← List.take_append_drop a I]
  rw [List.count_append]

theorem conflict_trans {I J K : List Bool} (h1 : Conflict I J) (h2 : Conflict J K) :
    Conflict I K := by
  unfold Conflict at h1 h2 ⊢
  obtain ⟨l1, fI, fJ, c1, t1⟩ := h1
  obtain ⟨l2, -, fK, c2, t2⟩ := h2
  refine ⟨by omega, fI, fK, c1.trans c2, ?_⟩
  obtain ⟨pa, la, ga, ta⟩ := lz_spec I fI
  obtain ⟨pb, lb, gb, tb⟩ := lz_spec J fJ
  rw [take_eq_iff] at t1 t2 ⊢
  have hJa : J[lastZero I - 1]? = some false := by
    rw [← t1 (lastZero I - 1) (by omega)]; exact ga
  have hab : lastZero I ≤ lastZero J := by
    by_contra hc
    push_neg at hc
    have := tb (lastZero I - 1) (by omega) (by omega)
    rw [hJa] at this
    simp at this
  intro i hi
  rw [t1 i hi, t2 i (by omega)]

theorem step (I1 I2 : List Bool) (h : Conflict I1 I2) (hlen : I1.length + 1 < I2.length) :
    ∃ J, Conflict I1 J ∧ Edge J I2 ∧ J.length + 1 = I2.length := by
  unfold Conflict at h
  obtain ⟨hl, f1, f2, hc, ht⟩ := h
  obtain ⟨pa, la, ga, ta⟩ := lz_spec I1 f1
  obtain ⟨pb, lb, gb, tb⟩ := lz_spec I2 f2
  have hal : lastZero I1 < lastZero I2 := by
    by_contra hc'
    push_neg at hc'
    have e1 := count_split I1 (lastZero I1)
    have e2 := count_split I2 (lastZero I1)
    have d1 := count_drop I1 (lastZero I1) ta
    have d2 := count_drop I2 (lastZero I1) (fun i hi1 hi2 => tb i (by omega) hi2)
    unfold bitNorm at hc
    rw [ht] at e1
    omega
  rw [take_eq_iff] at ht
  obtain ⟨a, ha⟩ : ∃ a, a = lastZero I1 := ⟨_, rfl⟩
  obtain ⟨l, hl'⟩ : ∃ l, l = lastZero I2 := ⟨_, rfl⟩
  rw [← ha] at pa la ga ta ht hal
  rw [← hl'] at pb lb gb tb hal
  obtain ⟨J, hJ⟩ : ∃ J, J = I2.take (l - 1) ++ I2.drop l := ⟨_, rfl⟩
  have htl : (I2.take (l - 1)).length = l - 1 := by
    rw [List.length_take]; exact min_eq_left (by omega)
  have hJlen : J.length = I2.length - 1 := by
    rw [hJ, List.length_append, htl, List.length_drop]; omega
  have hJlt : ∀ i, i < l - 1 → J[i]? = I2[i]? := by
    intro i hi
    rw [hJ, List.getElem?_append_left (l₁ := I2.take (l - 1)) (l₂ := I2.drop l) (i := i) (by omega),
      List.getElem?_take, if_pos hi]
  have hJge : ∀ i, l - 1 ≤ i → J[i]? = I2[i + 1]? := by
    intro i hi
    rw [hJ, List.getElem?_append_right (l₁ := I2.take (l - 1)) (l₂ := I2.drop l) (i := i) (by omega),
      List.getElem?_drop, htl]
    congr 1
    omega
  have hd : I2.drop (l - 1) = false :: I2.drop l := by
    rw [List.drop_eq_getElem_cons (by omega : l - 1 < I2.length)]
    have e : l - 1 + 1 = l := by omega
    rw [e]
    congr 1
    have g := gb
    rw [List.getElem?_eq_getElem (l := I2) (i := l - 1) (by omega)] at g
    exact Option.some.inj g
  have e2 : I2.count true = (I2.take (l - 1)).count true + (I2.drop l).count true := by
    rw [count_split I2 (l - 1), hd, List.count_cons]
    simp
  have hJc : J.count true = I2.count true := by
    rw [hJ, List.count_append]; omega
  have fJ : false ∈ J := by
    have g : J[a - 1]? = some false := by
      rw [hJlt (a - 1) (by omega), ← ht (a - 1) (by omega)]; exact ga
    exact List.mem_of_getElem? g
  obtain ⟨pj, lj, gj, tj⟩ := lz_spec J fJ
  have hlzJ : lastZero J ≤ l - 1 := by
    by_contra hc'
    push_neg at hc'
    have g := hJge (lastZero J - 1) (by omega)
    have e : lastZero J - 1 + 1 = lastZero J := by omega
    rw [e, tb (lastZero J) (by omega) (by omega), gj] at g
    simp at g
  refine ⟨J, ?_, ?_, by omega⟩
  · unfold Conflict
    refine ⟨by omega, f1, fJ, ?_, ?_⟩
    · unfold bitNorm at hc ⊢; rw [hc, hJc]
    · rw [← ha, take_eq_iff]
      intro i hi
      rw [ht i hi, hJlt i (by omega)]
  · unfold Edge
    refine ⟨?_, by omega⟩
    unfold Conflict
    refine ⟨by omega, fJ, f2, ?_, ?_⟩
    · unfold bitNorm; exact hJc
    · rw [take_eq_iff]
      intro i hi
      exact hJlt i (by omega)

theorem forward (I1 : List Bool) : ∀ (n : ℕ) (I2 : List Bool),
    I2.length = I1.length + n + 1 → Conflict I1 I2 →
      ∃ P : List (List Bool), IsMonotonePath (I1 :: (P ++ [I2])) := by
  intro n
  induction n with
  | zero =>
    intro I2 hl h
    refine ⟨[], ?_⟩
    unfold IsMonotonePath
    rw [List.nil_append]
    exact List.isChain_pair.mpr ⟨h, by omega⟩
  | succ n ih =>
    intro I2 hl h
    obtain ⟨J, hJ1, hJ2, hJ3⟩ := step I1 I2 h (by omega)
    obtain ⟨P, hP⟩ := ih J (by omega) hJ1
    refine ⟨P ++ [J], ?_⟩
    unfold IsMonotonePath at hP ⊢
    have e : I1 :: ((P ++ [J]) ++ [I2]) = I1 :: (P ++ J :: I2 :: []) := by simp
    rw [e, List.isChain_cons_append_cons_cons]
    exact ⟨hP, hJ2, List.isChain_singleton _⟩

theorem backward : ∀ (P : List (List Bool)) (I1 I2 : List Bool),
    IsMonotonePath (I1 :: (P ++ [I2])) → Conflict I1 I2
  | [], I1, I2, h => by
    unfold IsMonotonePath at h
    rw [List.nil_append] at h
    exact (List.isChain_pair.mp h).1
  | x :: P, I1, I2, h => by
    unfold IsMonotonePath at h
    rw [List.cons_append, List.isChain_cons_cons] at h
    exact conflict_trans h.1.1 (backward P x I2 h.2)



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


/-! ### Stopping probabilities of last-zero strategies -/

theorem desc_of_conflict {J I : List Bool} (h : Conflict J I) : IsDescendant J I := by
  have hl : J.length < I.length := by unfold Conflict at h; exact h.1
  obtain ⟨n, hn⟩ : ∃ n, I.length = J.length + n + 1 := ⟨I.length - J.length - 1, by omega⟩
  exact forward J n I hn h

theorem conflict_of_desc {J I : List Bool} (h : IsDescendant J I) : Conflict J I := by
  obtain ⟨P, hP⟩ := h
  exact backward P J I hP

theorem lz_lt {I1 I2 : List Bool} (h : Conflict I1 I2) : lastZero I1 < lastZero I2 := by
  unfold Conflict at h
  obtain ⟨hl, f1, f2, hc, ht⟩ := h
  obtain ⟨pa, la, ga, ta⟩ := lz_spec I1 f1
  obtain ⟨pb, lb, gb, tb⟩ := lz_spec I2 f2
  by_contra hc'
  push_neg at hc'
  have e1 := count_split I1 (lastZero I1)
  have e2 := count_split I2 (lastZero I1)
  have d1 := count_drop I1 (lastZero I1) ta
  have d2 := count_drop I2 (lastZero I1) (fun i hi1 hi2 => tb i (by omega) hi2)
  unfold bitNorm at hc
  rw [ht] at e1
  omega

theorem lz_pos {I : List Bool} (h : false ∈ I) : 1 ≤ lastZero I := (lz_spec I h).1

theorem lz_le {I : List Bool} (h : false ∈ I) : lastZero I ≤ I.length := (lz_spec I h).2.1

theorem stop_nonneg (q : LZStrategy) (hq : IsLZStrategy q) (m : ℕ) (K : List Bool) (r : ℕ) :
    0 ≤ stopProbAt q m K r := by
  unfold stopProbAt
  apply mul_nonneg (hq _ _).1
  apply Finset.prod_nonneg
  intro j _
  exact sub_nonneg.mpr (hq _ _).2

theorem tel (a : ℕ → ℝ) (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 N, a r * ∏ j ∈ Finset.Ico 1 r, (1 - a j) =
      1 - ∏ j ∈ Finset.Ico 1 (N + 1), (1 - a j) := by
  induction N with
  | zero =>
    have h1 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    have h2 : Finset.Ico 1 (0 + 1) = (∅ : Finset ℕ) := Finset.Ico_eq_empty (by omega)
    rw [h1, h2, Finset.sum_empty, Finset.prod_empty]
    ring
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ N + 1 by omega), ih,
      Finset.prod_Ico_succ_top (show 1 ≤ N + 1 by omega)]
    ring

theorem stop_total (q : LZStrategy) (hq : IsLZStrategy q) (m : ℕ) (K : List Bool) (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 N, stopProbAt q m K r ≤ 1 := by
  unfold stopProbAt
  rw [tel (fun j => q m (K.take j)) N]
  apply sub_le_self
  apply Finset.prod_nonneg
  intro j _
  exact sub_nonneg.mpr (hq _ _).2

theorem sub_sum (F : ℕ → ℝ) (hF : ∀ r, 0 ≤ F r) (a b N : ℕ) (hab : a < b) (haN : a ≤ N) :
    F a + ∑ r ∈ Finset.Icc b N, F r ≤ ∑ r ∈ Finset.Icc a N, F r := by
  have hna : a ∉ Finset.Icc b N := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  rw [← Finset.sum_insert hna]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_insert, Finset.mem_Icc] at hx
    rw [Finset.mem_Icc]
    omega
  · intro x _ _
    exact hF x

theorem win_self (q : LZStrategy) {K : List Bool} (h : false ∈ K) :
    winLZ q K = stopProbAt q (bitNorm K) K (lastZero K) := by
  unfold winLZ
  rw [if_pos h]

theorem win_anc (q : LZStrategy) {I K : List Bool} (h : Conflict I K) :
    winLZ q I = stopProbAt q (bitNorm K) K (lastZero I) := by
  have h' := h
  unfold Conflict at h'
  obtain ⟨_, hfI, _, hbn, ht⟩ := h'
  rw [win_self q hfI, hbn]
  unfold stopProbAt
  have htj : ∀ j, j ≤ lastZero I → I.take j = K.take j := by
    intro j hj
    have e1 : (I.take (lastZero I)).take j = I.take j := by
      rw [List.take_take, min_eq_left hj]
    have e2 : (K.take (lastZero I)).take j = K.take j := by
      rw [List.take_take, min_eq_left hj]
    rw [← e1, ← e2, ht]
  rw [ht]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [htj j (by omega)]

theorem win_nonneg (q : LZStrategy) (hq : IsLZStrategy q) (I : List Bool) : 0 ≤ winLZ q I := by
  by_cases h : false ∈ I
  · rw [win_self q h]
    exact stop_nonneg q hq _ _ _
  · rw [win_nf q I h]
    norm_num

theorem win_le_one (q : LZStrategy) (hq : IsLZStrategy q) (I : List Bool) : winLZ q I ≤ 1 := by
  by_cases h : false ∈ I
  · rw [win_self q h]
    have h1 := stop_total q hq (bitNorm I) I (lastZero I)
    have h2 := Finset.single_le_sum (f := fun r => stopProbAt q (bitNorm I) I r)
      (fun r _ => stop_nonneg q hq _ _ r)
      (Finset.mem_Icc.mpr ⟨lz_pos h, le_refl (lastZero I)⟩)
    exact le_trans h2 h1
  · exact (win_nf q I h).le

theorem chain_bound (q : LZStrategy) (hq : IsLZStrategy q) :
    ∀ (P : List (List Bool)) (I K : List Bool), IsMonotonePath (I :: (P ++ [K])) →
      winLZ q I + ((P ++ [K]).map (winLZ q)).sum ≤
        ∑ r ∈ Finset.Icc (lastZero I) K.length, stopProbAt q (bitNorm K) K r
  | [], I, K, h => by
    have hc : Conflict I K := backward [] I K h
    have hc' := hc
    unfold Conflict at hc'
    have hfK : false ∈ K := hc'.2.2.1
    rw [List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, win_anc q hc,
      win_self q hfK]
    have hlt := lz_lt hc
    have hle := lz_le hfK
    have h1 := Finset.single_le_sum (f := fun r => stopProbAt q (bitNorm K) K r)
      (fun r _ => stop_nonneg q hq _ _ r)
      (Finset.mem_Icc.mpr ⟨le_refl (lastZero K), hle⟩)
    have h2 := sub_sum (fun r => stopProbAt q (bitNorm K) K r) (fun r => stop_nonneg q hq _ _ r)
      (lastZero I) (lastZero K) K.length hlt (by omega)
    beta_reduce at h1 h2
    linarith
  | J :: P, I, K, h => by
    have hc : Conflict I K := backward (J :: P) I K h
    have hc' := hc
    unfold Conflict at hc'
    have hfK : false ∈ K := hc'.2.2.1
    have h0 := h
    unfold IsMonotonePath at h0
    rw [List.cons_append, List.isChain_cons_cons] at h0
    have hIJ : Conflict I J := by
      have e := h0.1
      unfold Edge at e
      exact e.1
    have ih := chain_bound q hq P J K h0.2
    rw [List.cons_append, List.map_cons, List.sum_cons, win_anc q hc]
    have hlt := lz_lt hIJ
    have hlt2 := lz_lt hc
    have hle := lz_le hfK
    have h2 := sub_sum (fun r => stopProbAt q (bitNorm K) K r) (fun r => stop_nonneg q hq _ _ r)
      (lastZero I) (lastZero J) K.length hlt (by omega)
    beta_reduce at h2
    linarith

theorem valid_win (q : LZStrategy) (hq : IsLZStrategy q) : IsValidSel (winLZ q) := by
  unfold IsValidSel
  refine ⟨win_nonneg q hq, ?_⟩
  intro P hP
  match P, hP with
  | [], _ => simp
  | [I], _ => simpa using win_le_one q hq I
  | I :: J :: rest, hP =>
    obtain ⟨L, K, hLK⟩ : ∃ L K, J :: rest = L ++ [K] := by
      rcases List.eq_nil_or_concat (J :: rest) with h | ⟨L, K, h⟩
      · exact absurd h (List.cons_ne_nil _ _)
      · exact ⟨L, K, by rw [h, List.concat_eq_append]⟩
    rw [hLK] at hP ⊢
    have hb := chain_bound q hq L I K hP
    have hc : Conflict I K := backward L I K hP
    have hc' := hc
    unfold Conflict at hc'
    have hfI : false ∈ I := hc'.2.1
    have htot := stop_total q hq (bitNorm K) K K.length
    have hsub : ∑ r ∈ Finset.Icc (lastZero I) K.length, stopProbAt q (bitNorm K) K r ≤
        ∑ r ∈ Finset.Icc 1 K.length, stopProbAt q (bitNorm K) K r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        have := lz_pos hfI
        omega
      · intro x _ _
        exact stop_nonneg q hq _ _ x
    rw [List.map_cons, List.sum_cons]
    linarith


open Classical in
theorem rf_part (q : LZStrategy) (hq : IsLZStrategy q) (I J K : List Bool)
    (hIJ : IsDescendant I J) (hJK : IsDescendant J K) :
    winLZ q I + winLZ q J ≤ removedFrac (winLZ q) K ∧
      winLZ q K ≤ 1 - winLZ q I - winLZ q J := by
  have c1 := conflict_of_desc hIJ
  have c2 := conflict_of_desc hJK
  have c3 := conflict_trans c1 c2
  have hIK : IsDescendant I K := desc_of_conflict c3
  have l1 : I.length < J.length := by unfold Conflict at c1; exact c1.1
  have l2 : J.length < K.length := by unfold Conflict at c2; exact c2.1
  have hfK : false ∈ K := by unfold Conflict at c2; exact c2.2.2.1
  have hfI : false ∈ I := by unfold Conflict at c1; exact c1.2.1
  constructor
  · unfold removedFrac
    have hg : ∀ s ∈ Finset.range K.length,
        0 ≤ ∑ X ∈ (strings s).filter (fun X => IsDescendant X K), winLZ q X := by
      intro s _
      exact Finset.sum_nonneg (fun X _ => win_nonneg q hq X)
    have hI : winLZ q I ≤ ∑ X ∈ (strings I.length).filter (fun X => IsDescendant X K), winLZ q X := by
      apply Finset.single_le_sum (f := winLZ q) (fun X _ => win_nonneg q hq X)
      rw [Finset.mem_filter, mem_strings]
      exact ⟨rfl, hIK⟩
    have hJ : winLZ q J ≤ ∑ X ∈ (strings J.length).filter (fun X => IsDescendant X K), winLZ q X := by
      apply Finset.single_le_sum (f := winLZ q) (fun X _ => win_nonneg q hq X)
      rw [Finset.mem_filter, mem_strings]
      exact ⟨rfl, hJK⟩
    have hne : I.length ≠ J.length := by omega
    have hsub : ({I.length, J.length} : Finset ℕ) ⊆ Finset.range K.length := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_range]
      omega
    have h3 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s hs _ => hg s hs)
    rw [Finset.sum_pair hne] at h3
    beta_reduce at h3
    linarith
  · have hlt1 := lz_lt c1
    have hlt2 := lz_lt c2
    have hle := lz_le hfK
    have hpos := lz_pos hfI
    rw [win_anc q c3, win_anc q c2, win_self q hfK]
    have h1 := Finset.single_le_sum (f := fun r => stopProbAt q (bitNorm K) K r)
      (fun r _ => stop_nonneg q hq _ _ r)
      (Finset.mem_Icc.mpr ⟨le_refl (lastZero K), hle⟩)
    have h2 := sub_sum (fun r => stopProbAt q (bitNorm K) K r) (fun r => stop_nonneg q hq _ _ r)
      (lastZero J) (lastZero K) K.length hlt2 (by omega)
    have h3 := sub_sum (fun r => stopProbAt q (bitNorm K) K r) (fun r => stop_nonneg q hq _ _ r)
      (lastZero I) (lastZero J) K.length hlt1 (by omega)
    have hsub : ∑ r ∈ Finset.Icc (lastZero I) K.length, stopProbAt q (bitNorm K) K r ≤
        ∑ r ∈ Finset.Icc 1 K.length, stopProbAt q (bitNorm K) K r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        omega
      · intro x _ _
        exact stop_nonneg q hq _ _ x
    have htot := stop_total q hq (bitNorm K) K K.length
    beta_reduce at h1 h2 h3
    linarith

end Aux_SecSampling_removed_fraction_adds_up

open SecSampling Aux_SecSampling_removed_fraction_adds_up in
theorem solution (q : LZStrategy) (hq : IsLZStrategy q) :
    (∀ I J K : List Bool, IsDescendant I J → IsDescendant J K →
      winLZ q I + winLZ q J ≤ removedFrac (winLZ q) K ∧
        winLZ q K ≤ 1 - winLZ q I - winLZ q J) ∧
    IsValidSel (winLZ q) :=
  ⟨fun I J K h1 h2 => rf_part q hq I J K h1 h2, valid_win q hq⟩

