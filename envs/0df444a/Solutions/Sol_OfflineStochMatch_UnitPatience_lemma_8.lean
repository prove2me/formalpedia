-- Prove2me | solution 1 for OfflineStochMatch.UnitPatience.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:18:10.499368+00:00
-- url     : https://prove2.me/submissions/cb0bb953-f250-47c4-9a2d-7a7d3f06a18a

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting
set_option autoImplicit false

open Finset OfflineStochMatch.UnitPatience

lemma oo_F (k : ℕ) (z : ℕ → ℝ) (hz : ∀ j ∈ Icc 1 k, 0 ≤ z j ∧ z j ≤ 1)
    (hsum : ∑ j ∈ Icc 1 k, z j ≤ 1) (i : ℕ) (hi : i ≤ k) :
    1 - Real.exp (-Fstar z i) ≤ Fcum z i ∧
    (1 - Real.exp (-1)) * Fstar z i ≤ 1 - Real.exp (-Fstar z i) := by
  have hsub : Icc 1 i ⊆ Icc 1 k := Finset.Icc_subset_Icc le_rfl hi
  constructor
  · unfold Fcum Fstar
    have h1 : ∏ j ∈ Icc 1 i, (1 - z j) ≤ ∏ j ∈ Icc 1 i, Real.exp (-z j) := by
      apply Finset.prod_le_prod
      · intro j hj
        have := hz j (hsub hj)
        linarith [this.2]
      · intro j _
        linarith [Real.add_one_le_exp (-z j)]
    rw [← Real.exp_sum, Finset.sum_neg_distrib] at h1
    linarith
  · have hF0 : 0 ≤ Fstar z i := Finset.sum_nonneg (fun j hj => (hz j (hsub hj)).1)
    have hF1 : Fstar z i ≤ 1 := by
      unfold Fstar
      refine le_trans ?_ hsum
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => (hz j hj).1)
    have hconv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
      (show (0:ℝ) ≤ 1 - Fstar z i by linarith) hF0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add] at hconv
    have : Real.exp (-Fstar z i) ≤ 1 - Fstar z i * (1 - Real.exp (-1)) := by
      have e : Fstar z i * (-1) = -Fstar z i := by ring
      rw [e] at hconv
      simp [Real.exp_zero] at hconv
      nlinarith [hconv]
    nlinarith


lemma oo_abel (w a : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Icc 1 m, w i * a i
      = ∑ l ∈ Icc 1 m, (w l - w (l + 1)) * (∑ i ∈ Icc 1 l, a i)
        + w (m + 1) * ∑ i ∈ Icc 1 m, a i := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ m + 1 by omega)]
    rw [ih]
    ring

lemma oo_Fcum_sum (z : ℕ → ℝ) (l : ℕ) :
    ∑ i ∈ Icc 1 l, z i * ∏ j ∈ Ico 1 i, (1 - z j) = Fcum z l := by
  induction l with
  | zero => simp [Fcum]
  | succ l ih =>
    have e : Icc 1 (l + 1) = insert (l + 1) (Icc 1 l) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have hn : (l + 1) ∉ Icc 1 l := by simp
    have e2 : Ico 1 (l + 1) = Icc 1 l := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [e, Finset.sum_insert hn, ih, e2]
    unfold Fcum
    rw [e, Finset.prod_insert hn]
    ring

theorem solution (k : ℕ) (z w : ℕ → ℝ) (hz : ∀ i ∈ Icc 1 k, 0 ≤ z i ∧ z i ≤ 1)
    (hsum : ∑ i ∈ Icc 1 k, z i ≤ 1) (hw : ∀ i ∈ Icc 1 k, 0 ≤ w i)
    (hmono : ∀ i ∈ Icc 1 k, ∀ j ∈ Icc 1 k, i ≤ j → w j ≤ w i) :
    (1 - Real.exp (-1)) * ∑ i ∈ Icc 1 k, w i * z i
      ≤ ∑ i ∈ Icc 1 k, w i * z i * ∏ j ∈ Ico 1 i, (1 - z j) := by
  -- extended weight
  set w' : ℕ → ℝ := fun i => if i ≤ k then w i else 0 with hw'
  have hww : ∀ i ∈ Icc 1 k, w' i = w i := by
    intro i hi; simp [hw', (mem_Icc.1 hi).2]
  have hA1 := oo_abel w' z k
  have hA2 := oo_abel w' (fun i => z i * ∏ j ∈ Ico 1 i, (1 - z j)) k
  have hk1 : w' (k + 1) = 0 := by simp [hw']
  rw [hk1, zero_mul, add_zero] at hA1 hA2
  have hl : ∀ i ∈ Icc 1 k, w i * z i = w' i * z i := fun i hi => by rw [hww i hi]
  have hl2 : ∀ i ∈ Icc 1 k, w i * z i * ∏ j ∈ Ico 1 i, (1 - z j)
      = w' i * (z i * ∏ j ∈ Ico 1 i, (1 - z j)) := fun i hi => by rw [hww i hi]; ring
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hl2, hA1, hA2]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hd : 0 ≤ w' l - w' (l + 1) := by
    have hlk := (mem_Icc.1 hl).2
    have hl1 := (mem_Icc.1 hl).1
    by_cases h : l + 1 ≤ k
    · have := hmono l hl (l + 1) (mem_Icc.2 ⟨by omega, h⟩) (by omega)
      simp only [hw', hlk, h, if_true]
      linarith
    · have : l = k := by omega
      subst this
      simp only [hw', le_refl, if_true, h, if_false]
      linarith [hw l hl]
  rw [oo_Fcum_sum]
  have key := (oo_F k z hz hsum l (mem_Icc.1 hl).2).2
  have key2 := (oo_F k z hz hsum l (mem_Icc.1 hl).2).1
  unfold Fstar at key
  have h3 := mul_le_mul_of_nonneg_left (key.trans key2) hd
  calc (1 - Real.exp (-1)) * ((w' l - w' (l + 1)) * ∑ i ∈ Icc 1 l, z i)
      = (w' l - w' (l + 1)) * ((1 - Real.exp (-1)) * ∑ i ∈ Icc 1 l, z i) := by ring
    _ ≤ _ := h3
