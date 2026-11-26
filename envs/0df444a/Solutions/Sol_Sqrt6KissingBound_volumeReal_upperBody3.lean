-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_upperBody3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:25:00.462986+00:00
-- url     : https://prove2.me/submissions/4cfb2d10-65a5-478b-a4c3-eab383761755

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_continuous_upperProfile3
import Theorems.Thm_Sqrt6KissingBound_upperProfile3_nonneg
import Theorems.Thm_Sqrt6KissingBound_upperProfile3_integral
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
private lemma s3_pos : 0 < s3_d3 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3_d3 ^ 2 = 3 := by norm_num [s3_d3]
private lemma a_le_one : a_d3 ≤ 1 := by
  dsimp [a_d3]
  nlinarith [s3_sq, s3_pos]
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real upperBody3 =
      ((2 : ℝ) / 3 - 3 * s3_d3 / 8) * unitBallVolumeReal 2 := by
  have h := volumeReal_rotationalProfile_Ioo 1
    (a := a_d3) (b := (1 : ℝ)) (g := upperProfile3) a_le_one
    continuous_upperProfile3 (by intro t ht; exact upperProfile3_nonneg t)
  simpa only [upperBody3, upperProfile3_integral] using h
end Sqrt6KissingBound
