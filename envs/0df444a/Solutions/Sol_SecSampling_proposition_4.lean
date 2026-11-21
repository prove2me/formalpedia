-- Prove2me | solution 1 for SecSampling.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:08:30.135434+00:00
-- url     : https://prove2.me/submissions/ce8486f5-ba41-46ff-98df-123afb91b329

import Mathlib
import Definitions.Def_SecSampling_LastZero
import Definitions.Def_SecSampling_FractionalSelection

namespace Aux_SecSampling_proposition_4

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


/-! ### Tree structure of the conflict graph -/

section TreeSec

open Classical

theorem children_eq (Q : List Bool) (t : ℕ) :
    (strings ((Q ++ false :: List.replicate t true).length + 1)).filter
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

theorem children_inj (Q : List Bool) (t : ℕ) :
    Set.InjOn
      (fun j => Q ++ false :: (List.replicate j true ++ false :: List.replicate (t - j) true))
      (Finset.range (t + 1) : Set ℕ) := by
  intro j1 _ j2 _ heq
  have heq' : Q ++ false :: (List.replicate j1 true ++ false :: List.replicate (t - j1) true) =
      Q ++ false :: (List.replicate j2 true ++ false :: List.replicate (t - j2) true) := heq
  have h := List.append_cancel_left heq'
  have h2 := (List.cons.inj h).2
  have h3 := congrArg (List.idxOf false) h2
  rw [idx_lemma _ _ (nf_replicate _), idx_lemma _ _ (nf_replicate _)] at h3
  simpa using h3

theorem sum_children (p : ℝ) (v : List Bool) :
    ∑ c ∈ (strings (v.length + 1)).filter (fun c => Edge v c), weight p c =
      (degree v : ℝ) * (1 - p) * weight p v := by
  by_cases hf : false ∈ v
  · obtain ⟨Q, t, rfl⟩ := decompR v hf
    rw [children_eq, Finset.sum_image (children_inj Q t), degreeR, weight_app]
    have hterm : ∀ j ∈ Finset.range (t + 1),
        weight p (Q ++ false :: (List.replicate j true ++ false :: List.replicate (t - j) true)) =
          weight p Q * ((1 - p) * p ^ t) * (1 - p) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [weight_child]
      have hp : p ^ j * p ^ (t - j) = p ^ t := by
        rw [← pow_add]
        congr 1
        omega
      rw [← hp]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  · have hempty : (strings (v.length + 1)).filter (fun c => Edge v c) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ he
      apply hf
      unfold Edge Conflict at he
      exact he.1.2.1
    rw [hempty, Finset.sum_empty, degree_nf v hf]
    simp

theorem parent_unique {e e' c : List Bool} (h : Edge e c) (h' : Edge e' c) : e = e' := by
  unfold Edge at h h'
  obtain ⟨Q, a, b, h1, h2⟩ := coreR _ _ h.1 h.2
  obtain ⟨Q', a', b', h1', h2'⟩ := coreR _ _ h'.1 h'.2
  have e0 := h2.symm.trans h2'
  have e1 : (Q ++ false :: List.replicate a true) ++ false :: List.replicate b true =
      (Q' ++ false :: List.replicate a' true) ++ false :: List.replicate b' true := by
    simpa using e0
  obtain ⟨e2, hb⟩ := uniqR e1
  obtain ⟨hQ, ha⟩ := uniqR e2
  rw [h1, h1', hQ, ha, hb]

theorem edge_desc {v c : List Bool} (h : Edge v c) : IsDescendant v c :=
  desc_of_conflict (by unfold Edge at h; exact h.1)

theorem desc_trans {a b c : List Bool} (h1 : IsDescendant a b) (h2 : IsDescendant b c) :
    IsDescendant a c :=
  desc_of_conflict (conflict_trans (conflict_of_desc h1) (conflict_of_desc h2))

theorem desc_len {a b : List Bool} (h : IsDescendant a b) : a.length < b.length := by
  have hc := conflict_of_desc h
  unfold Conflict at hc
  exact hc.1

theorem desc_last {u c : List Bool} (h : IsDescendant u c) :
    Edge u c ∨ ∃ e, IsDescendant u e ∧ Edge e c := by
  obtain ⟨P, hP⟩ := h
  unfold IsMonotonePath at hP
  rcases List.eq_nil_or_concat P with hP0 | ⟨P', e, hPe⟩
  · left
    rw [hP0, List.nil_append] at hP
    exact List.isChain_pair.mp hP
  · right
    rw [hPe, List.concat_eq_append] at hP
    have e1 : u :: (P' ++ [e] ++ [c]) = u :: (P' ++ e :: c :: []) := by simp
    rw [e1, List.isChain_cons_append_cons_cons] at hP
    exact ⟨e, ⟨P', hP.1⟩, hP.2.1⟩

theorem has_parent {u c : List Bool} (h : IsDescendant u c) : ∃ e, Edge e c := by
  rcases desc_last h with h1 | ⟨e, _, h2⟩
  · exact ⟨u, h1⟩
  · exact ⟨e, h2⟩

theorem anc_child {v c u : List Bool} (hvc : Edge v c) :
    IsDescendant u c ↔ u = v ∨ IsDescendant u v := by
  constructor
  · intro h
    rcases desc_last h with h1 | ⟨e, he1, he2⟩
    · left
      exact parent_unique h1 hvc
    · right
      rw [parent_unique he2 hvc] at he1
      exact he1
  · rintro (h | h)
    · rw [h]
      exact edge_desc hvc
    · exact desc_trans h (edge_desc hvc)

theorem rf_child (q : List Bool → ℝ) {v c : List Bool} (h : Edge v c) :
    removedFrac q c = removedFrac q v + q v := by
  unfold removedFrac
  have hl : c.length = v.length + 1 := by unfold Edge at h; exact h.2
  rw [hl, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext u
    simp only [Finset.mem_filter, mem_strings]
    rw [anc_child h]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rcases h2 with h2 | h2
      · exfalso
        rw [h2] at h1
        omega
      · exact h2
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inr h2⟩
  · have hset : (strings v.length).filter (fun u => IsDescendant u c) = {v} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_singleton, mem_strings]
      rw [anc_child h]
      constructor
      · rintro ⟨h1, h2⟩
        rcases h2 with h2 | h2
        · exact h2
        · exfalso
          have := desc_len h2
          omega
      · rintro rfl
        exact ⟨rfl, Or.inl rfl⟩
    rw [hset, Finset.sum_singleton]

theorem rf_root (q : List Bool → ℝ) {c : List Bool} (h : ¬ ∃ e, Edge e c) :
    removedFrac q c = 0 := by
  unfold removedFrac
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.mem_filter] at hu
  exact absurd (has_parent hu.2) h

theorem rf_nonneg (q : List Bool → ℝ) (hq : ∀ I, 0 ≤ q I) (v : List Bool) :
    0 ≤ removedFrac q v :=
  Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun u _ => hq u))

theorem anc_path (q : List Bool → ℝ) : ∀ (N : ℕ) (v : List Bool), v.length ≤ N →
    ∃ P : List (List Bool), IsMonotonePath (P ++ [v]) ∧
      ((P ++ [v]).map q).sum = removedFrac q v + q v := by
  intro N
  induction N with
  | zero =>
    intro v hv
    have hroot : ¬ ∃ e, Edge e v := by
      rintro ⟨e, he⟩
      unfold Edge at he
      obtain ⟨_, h2⟩ := he
      omega
    refine ⟨[], ?_, ?_⟩
    · unfold IsMonotonePath
      rw [List.nil_append]
      exact List.isChain_singleton v
    · rw [rf_root q hroot]
      simp
  | succ N ih =>
    intro v hv
    by_cases hp : ∃ e, Edge e v
    · obtain ⟨e, he⟩ := hp
      have hel : v.length = e.length + 1 := by unfold Edge at he; exact he.2
      obtain ⟨P, hP1, hP2⟩ := ih e (by omega)
      refine ⟨P ++ [e], ?_, ?_⟩
      · unfold IsMonotonePath at hP1 ⊢
        have e1 : P ++ [e] ++ [v] = P ++ e :: v :: [] := by simp
        rw [e1, List.isChain_append_cons_cons]
        exact ⟨hP1, he, List.isChain_singleton v⟩
      · rw [List.map_append, List.sum_append, hP2, rf_child q he]
        simp
    · refine ⟨[], ?_, ?_⟩
      · unfold IsMonotonePath
        rw [List.nil_append]
        exact List.isChain_singleton v
      · rw [rf_root q hp]
        simp

theorem anc_bound (q : List Bool → ℝ) (hq : IsValidSel q) (v : List Bool) :
    removedFrac q v + q v ≤ 1 := by
  obtain ⟨P, h1, h2⟩ := anc_path q v.length v le_rfl
  rw [← h2]
  exact hq.2 _ h1

theorem count_take_le (Q : List Bool) (j : ℕ) : (Q.take j).count true ≤ Q.count true := by
  have := count_split Q j
  omega

theorem deg_conflict {J c : List Bool} (h : Conflict J c) : degree c ≤ degree J := by
  have h' := h
  unfold Conflict at h'
  obtain ⟨_, hJf, hcf, hbn, htk⟩ := h'
  have hlt := lz_lt h
  obtain ⟨A, u, rfl⟩ := decompR J hJf
  obtain ⟨B, b, rfl⟩ := decompR c hcf
  rw [degreeR, degreeR]
  rw [lzR, lzR] at hlt
  rw [lzR, tk, List.take_append_of_le_length (l₁ := B) (l₂ := false :: List.replicate b true)
    (i := A.length + 1) (by omega)] at htk
  rw [bitNorm_R, bitNorm_R] at hbn
  have h3 := count_take_le B (A.length + 1)
  rw [← htk, List.count_append] at h3
  have h4 : List.count true [false] = 0 := by decide
  omega

theorem weight_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (v : List Bool) : 0 ≤ weight p v := by
  unfold weight
  exact mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)

theorem deg_le_real (p : ℝ) (hp1 : p < 1) {d : ℕ} (h : d ≤ kOf p) : (d : ℝ) * (1 - p) ≤ 1 := by
  have h1 : (0 : ℝ) < 1 - p := by linarith
  have h2 : ((kOf p : ℕ) : ℝ) ≤ 1 / (1 - p) := by
    unfold kOf
    exact Nat.floor_le (div_nonneg zero_le_one h1.le)
  have h3 : (d : ℝ) ≤ 1 / (1 - p) := le_trans (by exact_mod_cast h) h2
  rw [le_div_iff₀ h1] at h3
  exact h3

theorem deg_gt_real (p : ℝ) (hp1 : p < 1) {d : ℕ} (h : kOf p < d) : 1 ≤ (d : ℝ) * (1 - p) := by
  have h1 : (0 : ℝ) < 1 - p := by linarith
  have h2 : 1 / (1 - p) < (kOf p : ℝ) + 1 := by
    unfold kOf
    exact Nat.lt_floor_add_one _
  have h3' : kOf p + 1 ≤ d := h
  have h3 : (kOf p : ℝ) + 1 ≤ d := by exact_mod_cast h3'
  have h4 : 1 / (1 - p) < d := by linarith
  rw [div_lt_iff₀ h1] at h4
  linarith

theorem sum_split {S : Finset (List Bool)} (f : List Bool → ℝ) (P Q R : List Bool → Prop)
    (h : ∀ x ∈ S, (P x ↔ Q x ∨ R x) ∧ ¬ (Q x ∧ R x)) :
    ∑ x ∈ S.filter P, f x = ∑ x ∈ S.filter Q, f x + ∑ x ∈ S.filter R, f x := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨h1, h2⟩ := h x hx
  by_cases hQ : Q x <;> by_cases hR : R x <;> simp_all

end TreeSec


/-! ### The fill-in strategy -/

section FillSec

open Classical

def Fl (p : ℝ) (n t : ℕ) (v : List Bool) : Prop := v ∈ fillSet p n t v.length

def Rm (p : ℝ) (n t : ℕ) (v : List Bool) : Prop :=
  ∃ J, J ∈ fillSet p n t J.length ∧ IsDescendant J v

def FR (p : ℝ) (n t : ℕ) (v : List Bool) : Prop := Fl p n t v ∨ Rm p n t v

theorem mem_fill (p : ℝ) (n t : ℕ) {J : List Bool} {s : ℕ} :
    J ∈ fillSet p n t s ↔ (n ≤ s ∧ s ≤ n + t) ∧ J.length = s ∧
      (s < n + t → degree J ≤ kOf p) ∧
      ∀ s' : Fin s, ∀ J' ∈ fillSet p n t s', ¬ IsDescendant J' J := by
  rw [fillSet]
  split_ifs with h
  · rw [Finset.mem_filter, mem_strings]
    exact ⟨fun h' => ⟨h, h'.1, h'.2.1, h'.2.2⟩, fun h' => ⟨h'.2.1, h'.2.2.1, h'.2.2.2⟩⟩
  · constructor
    · intro h'
      simp at h'
    · intro h'
      exact absurd h'.1 h

theorem fill_len (p : ℝ) (n t : ℕ) {J : List Bool} {s : ℕ} (h : J ∈ fillSet p n t s) :
    J.length = s :=
  ((mem_fill p n t).mp h).2.1

theorem fill_iff (p : ℝ) (n t : ℕ) (v : List Bool) :
    Fl p n t v ↔ (n ≤ v.length ∧ v.length ≤ n + t) ∧ (v.length < n + t → degree v ≤ kOf p) ∧
      ¬ Rm p n t v := by
  unfold Fl Rm
  rw [mem_fill p n t]
  constructor
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨h1, h3, ?_⟩
    rintro ⟨J, hJ, hD⟩
    exact h4 ⟨J.length, desc_len hD⟩ J hJ hD
  · rintro ⟨h1, h3, h4⟩
    refine ⟨h1, rfl, h3, ?_⟩
    intro s' J' hJ' hD
    apply h4
    refine ⟨J', ?_, hD⟩
    rw [fill_len p n t hJ']
    exact hJ'

theorem fl_not_rm (p : ℝ) (n t : ℕ) {v : List Bool} (h : Fl p n t v) : ¬ Rm p n t v :=
  ((fill_iff p n t v).mp h).2.2

theorem rm_low (p : ℝ) (n t : ℕ) (v : List Bool) (h : v.length ≤ n) : ¬ Rm p n t v := by
  rintro ⟨J, hJ, hD⟩
  have h1 := ((mem_fill p n t).mp hJ).1.1
  have h2 := desc_len hD
  omega

theorem fr_child (p : ℝ) (n t : ℕ) {v c : List Bool} (h : Edge v c) (hv : FR p n t v) :
    Rm p n t c := by
  rcases hv with hv | ⟨J, hJ, hD⟩
  · exact ⟨v, hv, edge_desc h⟩
  · exact ⟨J, hJ, desc_trans hD (edge_desc h)⟩

theorem free_child (p : ℝ) (n t : ℕ) {v c : List Bool} (h : Edge v c) (hv : ¬ FR p n t v) :
    ¬ Rm p n t c := by
  rintro ⟨J, hJ, hD⟩
  apply hv
  rcases (anc_child h).mp hD with hJv | hD'
  · left
    rw [← hJv]
    exact hJ
  · right
    exact ⟨J, hJ, hD'⟩

theorem rm_parent (p : ℝ) (n t : ℕ) {c : List Bool} (h : Rm p n t c) :
    ∃ v, Edge v c ∧ FR p n t v := by
  obtain ⟨J, hJ, hD⟩ := h
  obtain ⟨v, hv⟩ := has_parent hD
  refine ⟨v, hv, ?_⟩
  rcases (anc_child hv).mp hD with hJv | hD'
  · left
    rw [← hJv]
    exact hJ
  · right
    exact ⟨J, hJ, hD'⟩

theorem rm_deg (p : ℝ) (n t : ℕ) {c : List Bool} (h : Rm p n t c) (hc : c.length ≤ n + t) :
    degree c ≤ kOf p := by
  obtain ⟨J, hJ, hD⟩ := h
  have hl := desc_len hD
  have h2 := ((mem_fill p n t).mp hJ).2.2.1 (by omega)
  exact le_trans (deg_conflict (conflict_of_desc hD)) h2

theorem ch_disj (S : Finset (List Bool)) :
    Set.PairwiseDisjoint (↑S) (fun v : List Bool => (strings (v.length + 1)).filter (fun c => Edge v c)) := by
  intro v _ v' _ hne
  show Disjoint ((strings (v.length + 1)).filter (fun c => Edge v c))
    ((strings (v'.length + 1)).filter (fun c => Edge v' c))
  rw [Finset.disjoint_left]
  intro c hc hc'
  rw [Finset.mem_filter] at hc hc'
  exact hne (parent_unique hc.2 hc'.2)

theorem sum_split' {S : Finset (List Bool)} (f : List Bool → ℝ) (P Q R : List Bool → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (h : ∀ x ∈ S, (P x ↔ Q x ∨ R x) ∧ ¬ (Q x ∧ R x)) :
    ∑ x ∈ S.filter P, f x = ∑ x ∈ S.filter Q, f x + ∑ x ∈ S.filter R, f x := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨h1, h2⟩ := h x hx
  by_cases hQ : Q x <;> by_cases hR : R x <;> simp_all

noncomputable def Th (p : ℝ) (q : List Bool → ℝ) (n t s : ℕ) : ℝ :=
  ∑ v ∈ (strings s).filter (fun v => ¬ FR p n t v), weight p v * removedFrac q v

noncomputable def Ps (p : ℝ) (q : List Bool → ℝ) (n t s : ℕ) : ℝ :=
  ∑ v ∈ (strings s).filter (fun v => FR p n t v), weight p v * (1 - removedFrac q v)

noncomputable def Fs (p : ℝ) (n t s : ℕ) : ℝ :=
  ∑ v ∈ (strings s).filter (fun v => Fl p n t v), weight p v

theorem free_step (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t : ℕ) (q : List Bool → ℝ)
    (hq : IsValidSel q) (s : ℕ) (hs1 : n ≤ s) (hs2 : s < n + t) :
    ∑ v ∈ (strings s).filter (fun v => ¬ FR p n t v), weight p v * q v ≤
      Th p q n t (s + 1) - Th p q n t s +
        ∑ v ∈ (strings (s + 1)).filter (fun v => Fl p n t v), weight p v * removedFrac q v := by
  have per : ∀ v ∈ (strings s).filter (fun v => ¬ FR p n t v),
      weight p v * q v + weight p v * removedFrac q v ≤
        ∑ c ∈ (strings (v.length + 1)).filter (fun c => Edge v c),
          weight p c * removedFrac q c := by
    intro v hv
    rw [Finset.mem_filter, mem_strings] at hv
    obtain ⟨hvl, hvf⟩ := hv
    have hdeg : kOf p < degree v := by
      by_contra hd
      push_neg at hd
      apply hvf
      left
      rw [fill_iff]
      exact ⟨⟨by omega, by omega⟩, fun _ => hd, fun hr => hvf (Or.inr hr)⟩
    have hsum : ∑ c ∈ (strings (v.length + 1)).filter (fun c => Edge v c),
        weight p c * removedFrac q c =
        ∑ c ∈ (strings (v.length + 1)).filter (fun c => Edge v c),
          weight p c * (removedFrac q v + q v) :=
      Finset.sum_congr rfl (fun c hc => by rw [rf_child q (Finset.mem_filter.mp hc).2])
    rw [hsum, ← Finset.sum_mul, sum_children]
    have h1 := deg_gt_real p hp1 hdeg
    have hA := rf_nonneg q hq.1 v
    have hw := weight_nonneg p hp0 hp1 v
    have hqv := hq.1 v
    have key := mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) hw) (add_nonneg hA hqv)
    nlinarith [key]
  have hsum2 := Finset.sum_le_sum per
  rw [Finset.sum_add_distrib, ← Finset.sum_biUnion (ch_disj _)] at hsum2
  have hsub : ((strings s).filter (fun v => ¬ FR p n t v)).biUnion
      (fun v : List Bool => (strings (v.length + 1)).filter (fun c => Edge v c)) ⊆
      (strings (s + 1)).filter (fun c => ¬ Rm p n t c) := by
    intro c hc
    rw [Finset.mem_biUnion] at hc
    obtain ⟨v, hv, hcv⟩ := hc
    rw [Finset.mem_filter, mem_strings] at hv hcv
    rw [Finset.mem_filter, mem_strings]
    exact ⟨by omega, free_child p n t hcv.2 hv.2⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun c _ _ => mul_nonneg (weight_nonneg p hp0 hp1 c) (rf_nonneg q hq.1 c))
  have hsplit := sum_split' (S := strings (s + 1)) (fun c => weight p c * removedFrac q c)
    (fun c => ¬ Rm p n t c) (fun c => ¬ FR p n t c) (fun c => Fl p n t c) (by
      intro x _
      beta_reduce
      have hx := fl_not_rm p n t (v := x)
      unfold FR
      constructor
      · constructor
        · intro h
          by_cases hf : Fl p n t x
          · right
            exact hf
          · left
            rintro (h1 | h1)
            · exact hf h1
            · exact h h1
        · rintro (h | h)
          · intro hr
            exact h (Or.inr hr)
          · exact hx h
      · rintro ⟨h1, h2⟩
        exact h1 (Or.inl h2))
  unfold Th
  linarith

theorem fr_step (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t : ℕ) (q : List Bool → ℝ)
    (hq : IsValidSel q) (s : ℕ) (hs1 : n ≤ s) (hs2 : s < n + t) :
    ∑ v ∈ (strings s).filter (fun v => FR p n t v), weight p v * q v ≤
      Ps p q n t s -
        ∑ c ∈ (strings (s + 1)).filter (fun c => Rm p n t c), weight p c * (1 - removedFrac q c) := by
  have per : ∀ v ∈ (strings s).filter (fun v => FR p n t v),
      weight p v * q v + ∑ c ∈ (strings (v.length + 1)).filter (fun c => Edge v c),
          weight p c * (1 - removedFrac q c) ≤ weight p v * (1 - removedFrac q v) := by
    intro v hv
    rw [Finset.mem_filter, mem_strings] at hv
    obtain ⟨hvl, hvfr⟩ := hv
    have hdeg : degree v ≤ kOf p := by
      rcases hvfr with hf | hr
      · exact ((fill_iff p n t v).mp hf).2.1 (by omega)
      · exact rm_deg p n t hr (by omega)
    have hsum : ∑ c ∈ (strings (v.length + 1)).filter (fun c => Edge v c),
        weight p c * (1 - removedFrac q c) =
        ∑ c ∈ (strings (v.length + 1)).filter (fun c => Edge v c),
          weight p c * (1 - (removedFrac q v + q v)) :=
      Finset.sum_congr rfl (fun c hc => by rw [rf_child q (Finset.mem_filter.mp hc).2])
    rw [hsum, ← Finset.sum_mul, sum_children]
    have h1 := deg_le_real p hp1 hdeg
    have hb := anc_bound q hq v
    have hw := weight_nonneg p hp0 hp1 v
    have key := mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) hw)
      (show 0 ≤ 1 - (removedFrac q v + q v) by linarith)
    nlinarith [key]
  have hsum2 := Finset.sum_le_sum per
  rw [Finset.sum_add_distrib, ← Finset.sum_biUnion (ch_disj _)] at hsum2
  have hsub : (strings (s + 1)).filter (fun c => Rm p n t c) ⊆
      ((strings s).filter (fun v => FR p n t v)).biUnion
        (fun v : List Bool => (strings (v.length + 1)).filter (fun c => Edge v c)) := by
    intro c hc
    rw [Finset.mem_filter, mem_strings] at hc
    obtain ⟨hcl, hcr⟩ := hc
    obtain ⟨v, hv, hfr⟩ := rm_parent p n t hcr
    have hvl : c.length = v.length + 1 := by unfold Edge at hv; exact hv.2
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_strings]
      exact ⟨by omega, hfr⟩
    · rw [Finset.mem_filter, mem_strings]
      exact ⟨by omega, hv⟩
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun c => weight p c * (1 - removedFrac q c)) hsub
    (fun c _ _ => mul_nonneg (weight_nonneg p hp0 hp1 c)
      (by linarith [anc_bound q hq c, hq.1 c]))
  unfold Ps
  linarith

theorem last_step (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t : ℕ) (q : List Bool → ℝ)
    (hq : IsValidSel q) :
    ∑ v ∈ strings (n + t), weight p v * q v ≤ Ps p q n t (n + t) ∧ Th p q n t (n + t) = 0 := by
  have hall : ∀ v ∈ strings (n + t), FR p n t v := by
    intro v hv
    rw [mem_strings] at hv
    by_contra hc
    unfold FR at hc
    push_neg at hc
    apply hc.1
    rw [fill_iff]
    exact ⟨⟨by omega, by omega⟩, fun h => absurd h (by omega), hc.2⟩
  constructor
  · unfold Ps
    rw [Finset.filter_true_of_mem hall]
    apply Finset.sum_le_sum
    intro v _
    have h1 := anc_bound q hq v
    have hw := weight_nonneg p hp0 hp1 v
    exact mul_le_mul_of_nonneg_left (by linarith) hw
  · unfold Th
    rw [Finset.filter_false_of_mem (fun v hv => not_not.mpr (hall v hv)), Finset.sum_empty]

theorem first_step (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t : ℕ) (q : List Bool → ℝ)
    (hq : IsValidSel q) :
    -(Th p q n t n - Ps p q n t n) ≤ Fs p n t n := by
  have h1 : Ps p q n t n ≤ ∑ v ∈ (strings n).filter (fun v => FR p n t v), weight p v := by
    unfold Ps
    apply Finset.sum_le_sum
    intro v _
    have h2 := rf_nonneg q hq.1 v
    have hw := weight_nonneg p hp0 hp1 v
    nlinarith
  have h2 : (strings n).filter (fun v => FR p n t v) = (strings n).filter (fun v => Fl p n t v) := by
    apply Finset.filter_congr
    intro v hv
    rw [mem_strings] at hv
    unfold FR
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h (rm_low p n t v (by omega))
    · intro h
      exact Or.inl h
  have h3 : 0 ≤ Th p q n t n :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (weight_nonneg p hp0 hp1 v) (rf_nonneg q hq.1 v))
  have h4 : Fs p n t n = ∑ v ∈ (strings n).filter (fun v => FR p n t v), weight p v := by
    unfold Fs
    rw [h2]
  linarith

theorem ps_split (p : ℝ) (n t : ℕ) (q : List Bool → ℝ) (s : ℕ) :
    Ps p q n t s =
      ∑ c ∈ (strings s).filter (fun c => Rm p n t c), weight p c * (1 - removedFrac q c) +
      ∑ c ∈ (strings s).filter (fun c => Fl p n t c), weight p c * (1 - removedFrac q c) := by
  unfold Ps
  apply sum_split'
  intro x _
  beta_reduce
  unfold FR
  constructor
  · exact or_comm
  · rintro ⟨h1, h2⟩
    exact fl_not_rm p n t h2 h1

theorem fs_split (p : ℝ) (n t : ℕ) (q : List Bool → ℝ) (s : ℕ) :
    Fs p n t s =
      ∑ c ∈ (strings s).filter (fun c => Fl p n t c), weight p c * removedFrac q c +
      ∑ c ∈ (strings s).filter (fun c => Fl p n t c), weight p c * (1 - removedFrac q c) := by
  unfold Fs
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem gain_split (p : ℝ) (n t : ℕ) (q : List Bool → ℝ) (s : ℕ) :
    perfSel p q s = ∑ v ∈ (strings s).filter (fun v => ¬ FR p n t v), weight p v * q v +
      ∑ v ∈ (strings s).filter (fun v => FR p n t v), weight p v * q v := by
  unfold perfSel
  rw [← Finset.sum_filter_add_sum_filter_not (strings s) (fun v => FR p n t v)]
  ring

theorem perf_fill (p : ℝ) (n t s : ℕ) : perfSel p (fillIn p n t) s = Fs p n t s := by
  unfold perfSel Fs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  unfold fillIn Fl
  split_ifs <;> simp_all

theorem chain_conflict : ∀ (P : List (List Bool)) (x : List Bool), List.IsChain Edge (x :: P) →
    ∀ y ∈ P, Conflict x y
  | [], x, _, y, hy => by simp at hy
  | z :: P, x, h, y, hy => by
    rw [List.isChain_cons_cons] at h
    have hxz : Conflict x z := by
      have e := h.1
      unfold Edge at e
      exact e.1
    rcases List.mem_cons.mp hy with hyz | hy'
    · rw [hyz]
      exact hxz
    · exact conflict_trans hxz (chain_conflict P z h.2 y hy')

theorem fill_path (p : ℝ) (n t : ℕ) : ∀ (P : List (List Bool)) (x : List Bool),
    List.IsChain Edge (x :: P) → ((x :: P).map (fillIn p n t)).sum ≤ 1
  | [], x, _ => by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold fillIn
    split_ifs <;> norm_num
  | z :: P, x, h => by
    rw [List.map_cons, List.sum_cons]
    by_cases hx : x ∈ fillSet p n t x.length
    · have hzero : ((z :: P).map (fillIn p n t)).sum = 0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨y, hy, hya⟩ := List.mem_map.mp ha
        rw [← hya]
        have hc := chain_conflict (z :: P) x h y hy
        unfold fillIn
        rw [if_neg]
        intro hy'
        have hl : x.length < y.length := by unfold Conflict at hc; exact hc.1
        exact ((mem_fill p n t).mp hy').2.2.2 ⟨x.length, hl⟩ x hx (desc_of_conflict hc)
      rw [hzero]
      unfold fillIn
      rw [if_pos hx]
      norm_num
    · have hx0 : fillIn p n t x = 0 := by
        unfold fillIn
        rw [if_neg hx]
      rw [hx0, zero_add]
      exact fill_path p n t P z (List.isChain_cons_cons.mp h).2

theorem fill_valid (p : ℝ) (n t : ℕ) : IsValidSel (fillIn p n t) := by
  unfold IsValidSel
  refine ⟨fun I => by unfold fillIn; split_ifs <;> norm_num, ?_⟩
  intro P hP
  match P, hP with
  | [], _ => simp
  | x :: P', hP => exact fill_path p n t P' x hP

theorem telescope (G F D : ℕ → ℝ) (n t : ℕ)
    (h1 : ∀ s, n ≤ s → s < n + t → G s ≤ D (s + 1) - D s + F (s + 1))
    (h2 : G (n + t) ≤ -D (n + t)) (h3 : -D n ≤ F n) :
    ∑ i ∈ Finset.range (t + 1), G (n + i) ≤ ∑ i ∈ Finset.range (t + 1), F (n + i) := by
  have key : ∀ j, j ≤ t → ∑ i ∈ Finset.range j, G (n + i) ≤
      D (n + j) - D n + ∑ i ∈ Finset.range j, F (n + (i + 1)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hs := h1 (n + j) (by omega) (by omega)
      have e : n + (j + 1) = n + j + 1 := by ring
      rw [e]
      linarith [ih (by omega)]
  have k := key t le_rfl
  rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.add_zero]
  linarith

theorem window_opt (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t : ℕ) (q : List Bool → ℝ)
    (hq : IsValidSel q) : windowAvg p q n t ≤ windowAvg p (fillIn p n t) n t := by
  unfold windowAvg
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hI : ∀ f : ℕ → ℝ, ∑ s ∈ Finset.Icc n (n + t), f s =
      ∑ i ∈ Finset.range (t + 1), f (n + i) := by
    intro f
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      show n + t + 1 - n = t + 1 by omega]
  rw [hI, hI]
  have hT := telescope (fun s => perfSel p q s) (fun s => Fs p n t s)
    (fun s => Th p q n t s - Ps p q n t s) n t
    (by
      intro s hs1 hs2
      beta_reduce
      have g := gain_split p n t q s
      have f1 := free_step p hp0 hp1 n t q hq s hs1 hs2
      have f2 := fr_step p hp0 hp1 n t q hq s hs1 hs2
      have ps := ps_split p n t q (s + 1)
      have fs := fs_split p n t q (s + 1)
      linarith)
    (by
      beta_reduce
      obtain ⟨l1, l2⟩ := last_step p hp0 hp1 n t q hq
      have g : perfSel p q (n + t) = ∑ v ∈ strings (n + t), weight p v * q v := rfl
      linarith)
    (by
      beta_reduce
      exact first_step p hp0 hp1 n t q hq)
  beta_reduce at hT
  have hF : ∑ i ∈ Finset.range (t + 1), perfSel p (fillIn p n t) (n + i) =
      ∑ i ∈ Finset.range (t + 1), Fs p n t (n + i) :=
    Finset.sum_congr rfl (fun i _ => perf_fill p n t (n + i))
  linarith

end FillSec


/-! ### k-max winners versus fill-in -/

section KWSec

open Classical

theorem kw_iff (p : ℝ) (v : List Bool) :
    winLZ (kmaxLZ p) v = 1 ↔ degree v ≤ kOf p ∧ ∀ u, IsDescendant u v → kOf p < degree u := by
  by_cases hf : false ∈ v
  swap
  · rw [win_nf _ v hf, degree_nf v hf]
    constructor
    · intro _
      refine ⟨Nat.zero_le _, fun u hu => ?_⟩
      have hc := conflict_of_desc hu
      unfold Conflict at hc
      exact absurd hc.2.2.1 hf
    · intro _
      rfl
  obtain ⟨Q, t, rfl⟩ := decompR v hf
  rw [win_kmax, degreeR]
  constructor
  · rintro ⟨ht, hall⟩
    refine ⟨by omega, ?_⟩
    intro J hD
    have hc := conflict_of_desc hD
    have hc' := hc
    unfold Conflict at hc'
    obtain ⟨hlt, hJf, _, hbn, htk⟩ := hc'
    obtain ⟨A, u, rfl⟩ := decompR J hJf
    rw [lzR, tk] at htk
    obtain ⟨R, hR⟩ : ∃ R, R = (Q ++ false :: List.replicate t true).drop (A.length + 1) :=
      ⟨_, rfl⟩
    have hIe : Q ++ false :: List.replicate t true = A ++ false :: R := by
      rw [hR]
      calc Q ++ false :: List.replicate t true
          = (Q ++ false :: List.replicate t true).take (A.length + 1) ++
              (Q ++ false :: List.replicate t true).drop (A.length + 1) :=
            (List.take_append_drop _ _).symm
        _ = A ++ false :: (Q ++ false :: List.replicate t true).drop (A.length + 1) := by
            rw [← htk]
            simp
    have hRl : R.length > u := by
      have := congrArg List.length hIe
      simp only [List.length_append, List.length_cons, List.length_replicate] at this hlt
      omega
    have hRc : R.count true = u := by
      have hbn2 := hbn
      rw [bitNorm_R, hIe] at hbn2
      unfold bitNorm at hbn2
      rw [List.count_append, ct_false_cons] at hbn2
      omega
    have hRf : false ∈ R := by
      by_contra hc2
      have := ct_of_nf R hc2
      omega
    obtain ⟨R', t', hR'⟩ := decompR R hRf
    rw [hR'] at hIe
    have hIe2 : Q ++ false :: List.replicate t true =
        (A ++ false :: R') ++ false :: List.replicate t' true := by
      rw [hIe]; simp
    obtain ⟨hQ, htt⟩ := uniqR hIe2
    have hQl : A.length + 1 ≤ Q.length := by
      rw [hQ]; simp only [List.length_append, List.length_cons]; omega
    have hQa : Q[A.length + 1 - 1]? = some false := by
      rw [hQ, Nat.add_sub_cancel, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero]
    have key := hall (A.length + 1) (by omega) hQl hQa
    have htk2 : Q.take (A.length + 1) = A ++ [false] := by
      rw [hQ, tk]
    rw [htk2, List.count_append] at key
    have hb2 : Q.count true + t = A.count true + u := by
      rw [bitNorm_R, bitNorm_R] at hbn
      omega
    have hfz : List.count true [false] = 0 := by decide
    rw [hfz] at key
    rw [degreeR]
    omega
  · rintro ⟨hdeg, hanc⟩
    refine ⟨by omega, ?_⟩
    intro j h1 h2 h3
    by_contra hc0
    push_neg at hc0
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h3
    have hil : i < Q.length := by omega
    have htki : Q.take (i + 1) = Q.take i ++ [false] := by
      rw [List.take_succ, h3, Option.toList_some]
    obtain ⟨A, hA⟩ : ∃ A, A = Q.take i := ⟨_, rfl⟩
    rw [← hA] at htki
    have hAl : A.length = i := by rw [hA, List.length_take]; exact min_eq_left (by omega)
    have hcA : (Q.take (i + 1)).count true = A.count true := by
      rw [htki, List.count_append]
      simp
    rw [hcA] at hc0
    have hAQ : A.count true ≤ Q.count true := by
      have := count_take_le Q (i + 1)
      omega
    have hsplit := count_split Q (i + 1)
    have hdrop : (Q.drop (i + 1)).count true ≤ Q.length - (i + 1) := by
      have := List.count_le_length (a := true) (l := Q.drop (i + 1))
      rw [List.length_drop] at this
      exact this
    obtain ⟨u, hu⟩ : ∃ u, u = Q.count true + t - A.count true := ⟨_, rfl⟩
    rw [← hu] at hc0
    have hconf : Conflict (A ++ false :: List.replicate u true)
        (Q ++ false :: List.replicate t true) := by
      unfold Conflict
      refine ⟨?_, by simp, by simp, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_replicate]
        omega
      · rw [bitNorm_R, bitNorm_R]
        omega
      · rw [lzR, tk, hAl, List.take_append_of_le_length (l₁ := Q)
          (l₂ := false :: List.replicate t true) (i := i + 1) (by omega), htki]
    have h4 := hanc _ (desc_of_conflict hconf)
    rw [degreeR] at h4
    omega

theorem notrm_aux (p : ℝ) (n t : ℕ) (v : List Bool) (hv : v.length ≤ n + t) :
    ∀ L (u : List Bool), u.length = L → IsDescendant u v → n ≤ u.length →
      degree u ≤ kOf p → Rm p n t v := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro u hL hD hn hd
    by_cases hex : ∃ u', IsDescendant u' u ∧ n ≤ u'.length ∧ degree u' ≤ kOf p
    · obtain ⟨u', h1, h2, h3⟩ := hex
      exact ih u'.length (by rw [← hL]; exact desc_len h1) u' rfl (desc_trans h1 hD) h2 h3
    · have hnr : ¬ Rm p n t u := by
        rintro ⟨J, hJ, hJD⟩
        apply hex
        have hm := (mem_fill p n t).mp hJ
        refine ⟨J, hJD, hm.1.1, hm.2.2.1 ?_⟩
        have := desc_len hJD
        have := desc_len hD
        omega
      have hfl : Fl p n t u :=
        (fill_iff p n t u).mpr ⟨⟨hn, by have := desc_len hD; omega⟩, fun _ => hd, hnr⟩
      exact ⟨u, hfl, hD⟩

theorem notrm_iff (p : ℝ) (n t : ℕ) (v : List Bool) (hv : v.length ≤ n + t) :
    ¬ Rm p n t v ↔ ∀ u, IsDescendant u v → n ≤ u.length → kOf p < degree u := by
  constructor
  · intro hr u hu hun
    by_contra hd
    push_neg at hd
    exact hr (notrm_aux p n t v hv u.length u rfl hu hun hd)
  · rintro hall ⟨J, hJ, hD⟩
    have hm := (mem_fill p n t).mp hJ
    have h1 := hall J hD hm.1.1
    have h2 := hm.2.2.1 (by have := desc_len hD; omega)
    omega

theorem fl_iff' (p : ℝ) (n t : ℕ) (v : List Bool) :
    Fl p n t v ↔ (n ≤ v.length ∧ v.length ≤ n + t) ∧ (v.length < n + t → degree v ≤ kOf p) ∧
      ∀ u, IsDescendant u v → n ≤ u.length → kOf p < degree u := by
  rw [fill_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (notrm_iff p n t v h1.2).mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (notrm_iff p n t v h1.2).mpr h3⟩

theorem exists_anc_at : ∀ (d : ℕ) (v u : List Bool) (L : ℕ), v.length = L + 1 + d →
    IsDescendant u v → u.length ≤ L →
      ∃ w : List Bool, w.length = L ∧ (w = u ∨ IsDescendant u w) ∧ IsDescendant w v := by
  intro d
  induction d with
  | zero =>
    intro v u L hv hD hu
    obtain ⟨e, he⟩ := has_parent hD
    have hel : v.length = e.length + 1 := by unfold Edge at he; exact he.2
    refine ⟨e, by omega, ?_, edge_desc he⟩
    rcases (anc_child he).mp hD with h | h
    · left
      exact h.symm
    · right
      exact h
  | succ d ih =>
    intro v u L hv hD hu
    obtain ⟨e, he⟩ := has_parent hD
    have hel : v.length = e.length + 1 := by unfold Edge at he; exact he.2
    rcases (anc_child he).mp hD with h | h
    · exfalso
      rw [h] at hu
      omega
    · obtain ⟨w, h1, h2, h3⟩ := ih e u L (by omega) h hu
      exact ⟨w, h1, h2, desc_trans h3 (edge_desc he)⟩

theorem kw_interior (p : ℝ) (n t : ℕ) (v : List Bool) (hs1 : n < v.length)
    (hs2 : v.length < n + t) : winLZ (kmaxLZ p) v = 1 ↔ Fl p n t v := by
  rw [kw_iff, fl_iff']
  constructor
  · rintro ⟨hd, hanc⟩
    exact ⟨⟨by omega, by omega⟩, fun _ => hd, fun u hu _ => hanc u hu⟩
  · rintro ⟨_, hd, hanc⟩
    refine ⟨hd (by omega), ?_⟩
    intro u hu
    by_cases hun : n ≤ u.length
    · exact hanc u hu hun
    · push_neg at hun
      obtain ⟨w, hw1, hw2, hw3⟩ := exists_anc_at (v.length - n - 1) v u n (by omega) hu (by omega)
      have hkw := hanc w hw3 (by omega)
      rcases hw2 with hw2 | hw2
      · rw [hw2] at hw1
        omega
      · have := deg_conflict (conflict_of_desc hw2)
        omega

theorem kw_fl (p : ℝ) (n t : ℕ) (v : List Bool) (h : winLZ (kmaxLZ p) v = 1)
    (hs1 : n ≤ v.length) (hs2 : v.length ≤ n + t) : Fl p n t v := by
  rw [kw_iff] at h
  rw [fl_iff']
  exact ⟨⟨hs1, hs2⟩, fun _ => h.1, fun u hu _ => h.2 u hu⟩

theorem mem_fillSet_iff (p : ℝ) (n t : ℕ) (I : List Bool) (s : ℕ) :
    I ∈ fillSet p n t s ↔ I.length = s ∧ Fl p n t I := by
  constructor
  · intro h
    refine ⟨fill_len p n t h, ?_⟩
    unfold Fl
    rw [fill_len p n t h]
    exact h
  · rintro ⟨h1, h2⟩
    unfold Fl at h2
    rw [h1] at h2
    exact h2

theorem mem_kw (p : ℝ) (I : List Bool) (s : ℕ) :
    I ∈ (strings s).filter (fun I => winLZ (kmaxLZ p) I = 1) ↔
      I.length = s ∧ winLZ (kmaxLZ p) I = 1 := by
  rw [Finset.mem_filter, mem_strings]

theorem deg_le_len (v : List Bool) : degree v ≤ v.length := by
  by_cases hf : false ∈ v
  · obtain ⟨Q, t, rfl⟩ := decompR v hf
    rw [degreeR]
    simp only [List.length_append, List.length_cons, List.length_replicate]
    omega
  · rw [degree_nf v hf]
    omega

theorem k_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : 1 ≤ kOf p := by
  have h1 : (0 : ℝ) < 1 - p := by linarith
  have h2 : (1 : ℝ) ≤ 1 / (1 - p) := by
    rw [le_div_iff₀ h1]
    linarith
  unfold kOf
  exact Nat.le_floor (by exact_mod_cast h2)

theorem no_anc_short {u v : List Bool} (h : IsDescendant u v) (hv : v.length ≤ 1) : False := by
  have hc := conflict_of_desc h
  unfold Conflict at hc
  obtain ⟨hl, hu, _⟩ := hc
  have hu0 : u.length = 0 := by omega
  rw [List.length_eq_zero_iff] at hu0
  rw [hu0] at hu
  simp at hu

theorem no_anc_one (Q : List Bool) (N : ℕ) (hQ : false ∉ Q) (u : List Bool)
    (h : IsDescendant u (Q ++ false :: List.replicate N true)) : False := by
  obtain ⟨e, he⟩ := has_parent h
  unfold Edge at he
  obtain ⟨Q', a, b, _, h2⟩ := coreR _ _ he.1 he.2
  have h3 := congrArg (List.count false) h2
  simp only [List.count_append, cf_false_cons, cf_rep] at h3
  have h4 : Q.count false = 0 := List.count_eq_zero.mpr hQ
  omega

theorem level_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (t : ℕ) (v : List Bool)
    (hv : v.length = 1) : winLZ (kmaxLZ p) v = 1 ∧ Fl p 1 t v := by
  have hk := k_pos p hp0 hp1
  have hd := deg_le_len v
  constructor
  · rw [kw_iff]
    exact ⟨by omega, fun u hu => (no_anc_short hu (by omega)).elim⟩
  · rw [fl_iff']
    exact ⟨⟨by omega, by omega⟩, fun _ => by omega, fun u hu _ => (no_anc_short hu (by omega)).elim⟩

end KWSec


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


section P4

open Classical

theorem kperf_val (p : ℝ) (s : ℕ) (hs : kOf p + 1 ≤ s) : kperf p s = guarantee p + p ^ s := by
  obtain ⟨j, rfl⟩ : ∃ j, s = kOf p + 1 + j := ⟨s - (kOf p + 1), by omega⟩
  exact kperf_big p j

theorem kperf_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (s : ℕ) : 0 ≤ kperf p s := by
  unfold kperf
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (weight_nonneg p hp0 hp1 v)
  unfold kind
  split_ifs <;> norm_num

theorem Fs_le_one (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t s : ℕ) : Fs p n t s ≤ 1 := by
  unfold Fs
  rw [← sum_weight p s]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun v _ _ => weight_nonneg p hp0 hp1 v)

theorem Fs_interior (p : ℝ) (n t s : ℕ) (h1 : n < s) (h2 : s < n + t) : Fs p n t s = kperf p s := by
  unfold Fs kperf
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mem_strings] at hv
  unfold kind
  have hiff := kw_interior p n t v (by omega) (by omega)
  by_cases hw : winLZ (kmaxLZ p) v = 1
  · rw [if_pos (hiff.mp hw), if_pos hw, mul_one]
  · rw [if_neg (fun h => hw (hiff.mpr h)), if_neg hw, mul_zero]

theorem Fs_bound (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t s : ℕ) (h1 : n ≤ s) (h2 : s ≤ n + t) :
    Fs p n t s ≤ kperf p s + (if s = n then 1 else 0) + (if s = n + t then 1 else 0) := by
  have hk := kperf_nonneg p hp0 hp1 s
  have hF := Fs_le_one p hp0 hp1 n t s
  by_cases e1 : s = n
  · rw [if_pos e1]
    have : (0 : ℝ) ≤ if s = n + t then 1 else 0 := by split_ifs <;> norm_num
    linarith
  · by_cases e2 : s = n + t
    · rw [if_neg e1, if_pos e2]
      linarith
    · rw [if_neg e1, if_neg e2, Fs_interior p n t s (by omega) (by omega)]
      linarith

theorem prop4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (q : LZStrategy) (hq : IsLZStrategy q)
    (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) : ∃ n : ℕ, N₀ ≤ n ∧ perfLZ p q n < guarantee p + ε := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one (half_pos hε) hp1
  obtain ⟨n, hn⟩ : ∃ n, n = max (max N₀ n0) (kOf p + 2) := ⟨_, rfl⟩
  have hn1 : N₀ ≤ n := by rw [hn]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hn2 : n0 ≤ n := by rw [hn]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hn3 : kOf p + 2 ≤ n := by rw [hn]; exact le_max_right _ _
  obtain ⟨t, ht⟩ : ∃ t : ℕ, 4 / ε < t := exists_nat_gt (4 / ε)
  have hvalid := valid_win q hq
  have hw := window_opt p hp0 hp1 n t (winLZ q) hvalid
  unfold windowAvg at hw
  have hpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right hpos] at hw
  have hcard : ((Finset.Icc n (n + t)).card : ℝ) = (t : ℝ) + 1 := by
    rw [Nat.card_Icc, show n + t + 1 - n = t + 1 by omega, Nat.cast_add, Nat.cast_one]
  have hlow : ((t : ℝ) + 1) * (guarantee p + ε) ≤
      ∑ s ∈ Finset.Icc n (n + t), perfSel p (winLZ q) s := by
    have h := Finset.sum_le_sum (s := Finset.Icc n (n + t))
      (f := fun _ => guarantee p + ε) (g := fun s => perfSel p (winLZ q) s)
      (fun s hs => by
        rw [Finset.mem_Icc] at hs
        exact hcon s (by omega))
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h
    exact h
  have hup1 : ∑ s ∈ Finset.Icc n (n + t), perfSel p (fillIn p n t) s ≤
      ∑ s ∈ Finset.Icc n (n + t),
        (kperf p s + (if s = n then 1 else 0) + (if s = n + t then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mem_Icc] at hs
    rw [perf_fill]
    exact Fs_bound p hp0 hp1 n t s hs.1 hs.2
  have hup2 : ∑ s ∈ Finset.Icc n (n + t),
      (kperf p s + (if s = n then (1 : ℝ) else 0) + (if s = n + t then 1 else 0)) =
      ∑ s ∈ Finset.Icc n (n + t), kperf p s + 1 + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.Icc n (n + t)) n,
      Finset.sum_ite_eq' (Finset.Icc n (n + t)) (n + t), if_pos (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩),
      if_pos (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]
  have hup3 : ∑ s ∈ Finset.Icc n (n + t), kperf p s ≤ ((t : ℝ) + 1) * (guarantee p + p ^ n) := by
    have h := Finset.sum_le_sum (s := Finset.Icc n (n + t))
      (f := fun s => kperf p s) (g := fun _ => guarantee p + p ^ n)
      (fun s hs => by
        rw [Finset.mem_Icc] at hs
        rw [kperf_val p s (by omega)]
        have := pow_le_pow_of_le_one hp0.le hp1.le hs.1
        linarith)
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h
    exact h
  have hpn : p ^ n < ε / 2 := lt_of_le_of_lt (pow_le_pow_of_le_one hp0.le hp1.le hn2) hn0
  have htε : 4 < (t : ℝ) * ε := by
    have := (div_lt_iff₀ hε).mp ht
    linarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hkey := mul_nonneg ht0 (show (0 : ℝ) ≤ ε / 2 - p ^ n by linarith)
  have hpn0 : 0 ≤ p ^ n := pow_nonneg hp0.le n
  nlinarith

end P4

end Aux_SecSampling_proposition_4

open SecSampling Aux_SecSampling_proposition_4 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (q : LZStrategy)
    (hq : IsLZStrategy q) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ perfLZ p q n < guarantee p + ε :=
  prop4 p hp0 hp1 q hq ε hε N₀

