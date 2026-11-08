-- Prove2me | solution 1 for OLPRegret.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:45:58.391329+00:00
-- url     : https://prove2.me/submissions/c33b86a5-82ba-4b8b-b2c1-40174a2193bf

import Mathlib
import Definitions.Def_OLPRegret_dualMin

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace Aux_OLP_l9
end Aux_OLP_l9

open OLPRegret in
theorem solution {m t : ℕ} (s : Sample m t) (b y y' : E m) (hb : VNonneg b) (hy : VNonneg y)
    (hy' : y' ∈ dualMin s b) :
    inner ℝ (y' - y) (LambdaDot s b y) ≤ 0 := by
  have hmin := hy'.2 y hy
  unfold Lambda at hmin
  unfold LambdaDot
  rw [inner_sub_right, inner_smul_right, inner_sum]
  have key : ∀ i, max (surplus (s i) y) 0 -
      inner ℝ (y' - y) (if 0 < surplus (s i) y then (s i).2 else 0) ≤ max (surplus (s i) y') 0 := by
    intro i
    split_ifs with h
    · rw [max_eq_left h.le]
      have : surplus (s i) y' = surplus (s i) y - inner ℝ (y' - y) (s i).2 := by
        unfold surplus
        rw [inner_sub_left, real_inner_comm (s i).2 y', real_inner_comm (s i).2 y]; ring
      rw [← this]; exact le_max_left _ _
    · rw [inner_zero_right, sub_zero, max_eq_right (not_lt.mp h)]; exact le_max_right _ _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => key i)
  rw [Finset.sum_sub_distrib] at hsum
  have ht : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg t)
  have h2 := mul_le_mul_of_nonneg_left hsum ht
  rw [mul_sub] at h2
  rw [div_eq_inv_mul, div_eq_inv_mul] at hmin
  have hb' : inner ℝ (y' - y) b = inner ℝ b y' - inner ℝ b y := by
    rw [inner_sub_left, real_inner_comm y' b, real_inner_comm y b]
  linarith
