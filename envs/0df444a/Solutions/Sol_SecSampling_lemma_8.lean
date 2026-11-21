-- Prove2me | solution 1 for SecSampling.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:01:00.693477+00:00
-- url     : https://prove2.me/submissions/8f95f0ba-e39a-437c-ab20-ee7deedfde2a

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

namespace Aux_SecSampling_lemma_8

open SecSampling

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

end Aux_SecSampling_lemma_8

open SecSampling in
theorem solution (I₁ I₂ : List Bool) :
    Conflict I₁ I₂ ↔ ∃ P : List (List Bool), IsMonotonePath (I₁ :: (P ++ [I₂])) := by
  constructor
  · intro h
    have hl : I₁.length < I₂.length := by unfold Conflict at h; exact h.1
    obtain ⟨n, hn⟩ : ∃ n, I₂.length = I₁.length + n + 1 := ⟨I₂.length - I₁.length - 1, by omega⟩
    exact Aux_SecSampling_lemma_8.forward I₁ n I₂ hn h
  · rintro ⟨P, hP⟩
    exact Aux_SecSampling_lemma_8.backward P I₁ I₂ hP
