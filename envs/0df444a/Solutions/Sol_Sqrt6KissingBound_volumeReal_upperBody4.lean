-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_upperBody4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:25:42.068382+00:00
-- url     : https://prove2.me/submissions/fe4e1f55-3194-44dc-92cf-6c8e8e165ec0

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_continuous_upperProfile4
import Theorems.Thm_Sqrt6KissingBound_upperProfile4_nonneg
import Theorems.Thm_Sqrt6KissingBound_upperProfile4_integral
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
set_option maxHeartbeats 800000
private lemma s3_pos : 0 < s3_d4 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3_d4 ^ 2 = 3 := by norm_num [s3_d4]
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real upperBody4 =
      ((33169 - 19150 * s3_d4) / 40) * unitBallVolumeReal 3 := by
  have h := volumeReal_rotationalProfile_Ioo 2
    (a := a_d4) (b := (1 : ℝ)) (g := upperProfile4)
    (by
      have hs : s3_d4 < 2 := by nlinarith [s3_sq, s3_pos]
      dsimp [a_d4]
      linarith)
    continuous_upperProfile4 (by intro t ht; exact upperProfile4_nonneg ht.1 ht.2)
  simpa [upperBody4, upperProfile4_integral] using h
end Sqrt6KissingBound
