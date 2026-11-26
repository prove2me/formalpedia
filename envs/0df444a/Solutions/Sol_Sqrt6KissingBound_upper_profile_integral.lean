-- Prove2me | solution 1 for Sqrt6KissingBound.upper_profile_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:21:04.725874+00:00
-- url     : https://prove2.me/submissions/726e4d9f-5217-4e54-9675-e36a5c4756f6

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_integral_const_mul_sub_pow
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
private lemma s3_sq : s3_bv ^ 2 = 3 := by norm_num [s3_bv]
private lemma upper_product : upperSlope_bv * (1 - a_bv) = (1 : ℝ) / 2 := by
  dsimp [upperSlope_bv, a_bv]
  nlinarith [s3_sq]
private lemma two_power_step (k : ℕ) :
    (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
private lemma upper_power_value (k : ℕ) :
    upperSlope_bv ^ (k + 1) * (1 - a_bv) ^ (k + 2) / (k + 2) =
      (2 - s3_bv) / ((k + 2) * 2 ^ (k + 2)) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  calc
    upperSlope_bv ^ (k + 1) * ((1 - a_bv) ^ (k + 1) * (1 - a_bv)) / (k + 2) =
        (upperSlope_bv * (1 - a_bv)) ^ (k + 1) * (1 - a_bv) / (k + 2) := by
      rw [mul_pow]
      ring
    _ = ((1 : ℝ) / 2) ^ (k + 1) * (1 - a_bv) / (k + 2) := by rw [upper_product]
    _ = (2 - s3_bv) / ((k + 2) * 2 ^ (k + 2)) := by
      dsimp [a_bv]
      simp only [two_power_step, div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
      ring_nf <;> norm_num
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) :
    (∫ t in a_bv..1, (upperSlope_bv * (1 - t)) ^ (k + 1)) =
      (2 - s3_bv) / ((k + 2) * 2 ^ (k + 2)) := by
  rw [integral_const_mul_sub_pow (k + 1)]
  convert upper_power_value k using 1 <;> norm_num [Nat.cast_add, add_assoc]
end Sqrt6KissingBound
