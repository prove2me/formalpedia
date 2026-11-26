-- Prove2me | solution 1 for Sqrt6KissingBound.bicone_profile_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:27:14.77438+00:00
-- url     : https://prove2.me/submissions/3b807f31-1bbc-41fb-925f-3b1a68a6d1d3

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Theorems.Thm_Sqrt6KissingBound_lower_profile_integral
import Theorems.Thm_Sqrt6KissingBound_upper_profile_integral
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
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
private lemma two_power_step (k : ℕ) :
    (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
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
    (∫ t in (0 : ℝ)..a_bv, (t / s3_bv) ^ (k + 1)) +
        (∫ t in a_bv..1, (upperSlope_bv * (1 - t)) ^ (k + 1)) =
      1 / ((k + 2) * 2 ^ (k + 1)) := by
  rw [lower_profile_integral, upper_profile_integral]
  simp only [two_power_step, div_eq_mul_inv, mul_inv_rev]
  ring
end Sqrt6KissingBound
