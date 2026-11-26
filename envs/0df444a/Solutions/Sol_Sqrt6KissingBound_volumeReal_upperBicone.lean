-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_upperBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:24:44.688215+00:00
-- url     : https://prove2.me/submissions/4bbd67fc-c158-4789-b556-3a65ba4d4853

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Theorems.Thm_Sqrt6KissingBound_upper_profile_integral
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_volumeReal_rotationalProfile_Ioo
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
private lemma s3_pos : 0 < s3_bv := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3_bv ^ 2 = 3 := by norm_num [s3_bv]
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
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real (upperBicone k) =
      ((2 - s3_bv) / ((k + 2) * 2 ^ (k + 2))) * unitBallVolumeReal (k + 1) := by
  have h := volumeReal_rotationalProfile_Ioo k
    (a := a_bv) (b := (1 : ℝ)) (g := fun t => upperSlope_bv * (1 - t))
    (by
      have hs : s3_bv < 2 := by nlinarith [s3_sq, s3_pos]
      dsimp [a_bv]
      linarith)
    (continuous_const.mul (continuous_const.sub continuous_id))
    (by
      intro t ht
      have : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      positivity)
  simpa [upperBicone, upper_profile_integral] using h
end Sqrt6KissingBound
