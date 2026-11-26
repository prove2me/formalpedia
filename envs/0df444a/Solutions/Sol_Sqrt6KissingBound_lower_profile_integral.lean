-- Prove2me | solution 1 for Sqrt6KissingBound.lower_profile_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:59.696816+00:00
-- url     : https://prove2.me/submissions/a00854a8-37c4-461a-a699-026ffa710122

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_integral_div_mul_pow
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
private lemma s3_pos : 0 < s3_bv := Real.sqrt_pos.2 (by norm_num)
private lemma s3_ne : s3_bv ≠ 0 := s3_pos.ne'
private lemma lower_power_value (k : ℕ) :
    a_bv ^ (k + 2) / (s3_bv ^ (k + 1) * (k + 2)) =
      s3_bv / ((k + 2) * 2 ^ (k + 2)) := by
  have hk : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  dsimp [a_bv]
  rw [div_pow]
  field_simp [s3_ne, hk]
  ring
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
    (∫ t in (0 : ℝ)..a_bv, (t / s3_bv) ^ (k + 1)) =
      s3_bv / ((k + 2) * 2 ^ (k + 2)) := by
  rw [integral_div_mul_pow (k + 1) s3_ne]
  convert lower_power_value k using 1 <;> norm_num [Nat.cast_add, add_assoc]
end Sqrt6KissingBound
