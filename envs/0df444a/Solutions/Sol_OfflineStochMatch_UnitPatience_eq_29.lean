-- Prove2me | solution 1 for OfflineStochMatch.UnitPatience.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:16:35.184642+00:00
-- url     : https://prove2.me/submissions/b069e6d0-e152-4c51-88df-d245d4161b5f

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

theorem solution (k : ℕ) (z : ℕ → ℝ) (hz : ∀ j ∈ Icc 1 k, 0 ≤ z j ∧ z j ≤ 1)
    (hsum : ∑ j ∈ Icc 1 k, z j ≤ 1) (i : ℕ) (hi : i ≤ k) :
    1 - Real.exp (-Fstar z i) ≤ Fcum z i ∧
    (1 - Real.exp (-1)) * Fstar z i ≤ 1 - Real.exp (-Fstar z i) :=
  oo_F k z hz hsum i hi
