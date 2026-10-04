-- Prove2me | solution 1 for SennottDP.ResidualLife.residual_moment_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:00:55.134745+00:00
-- url     : https://prove2.me/submissions/284d3913-314c-4372-b7f6-79fd165de172

import Mathlib
import Definitions.Def_SennottDP_ResidualLife_MSDist

open scoped ENNReal NNReal

set_option autoImplicit false

open SennottDP.ResidualLife in
theorem SennottDP_ResidualLife_residualMoment_le (u : ℕ → ℝ≥0∞) (s k : ℕ) :
    residualMoment u s k ≤ moment u k * (tail u s)⁻¹ := by
  unfold residualMoment moment
  calc ∑' y : ℕ, (y : ℝ≥0∞) ^ k * residualDist u s y
      ≤ ∑' y : ℕ, (((s + y : ℕ) : ℝ≥0∞) ^ k * u (s + y)) * (tail u s)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        unfold residualDist
        split_ifs with h
        · rw [div_eq_mul_inv, ← mul_assoc]
          gcongr
          exact_mod_cast Nat.le_add_left y s
        · simp
    _ = (∑' y : ℕ, ((s + y : ℕ) : ℝ≥0∞) ^ k * u (s + y)) * (tail u s)⁻¹ :=
        ENNReal.tsum_mul_right
    _ ≤ (∑' n : ℕ, (n : ℝ≥0∞) ^ k * u n) * (tail u s)⁻¹ := by
        exact mul_le_mul_of_nonneg_right (ENNReal.tsum_comp_le_tsum_of_injective (f := fun y : ℕ => s + y)
          (add_right_injective s) (fun n : ℕ => (n : ℝ≥0∞) ^ k * u n)) (by positivity)

open SennottDP.ResidualLife ENNReal NNReal in
theorem solution (u : ℕ → ℝ≥0∞) (hu : IsDistOnPos u) (k : ℕ) (hk : 1 ≤ k)
    (hmom : moment u k < ∞) (s : ℕ) (hs : 0 < tail u s) :
    residualMoment u s k < ∞ := by
  exact lt_of_le_of_lt (SennottDP_ResidualLife_residualMoment_le u s k)
    (ENNReal.mul_lt_top hmom (ENNReal.inv_lt_top.2 hs))
