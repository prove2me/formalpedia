-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_five_gt_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:18:32.347302+00:00
-- url     : https://prove2.me/submissions/bb88c874-388a-4f42-883c-d8c7e3c823d3

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_pi_lt_22_div_7
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_five
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_six

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution : unitBallVolumeReal 6 < unitBallVolumeReal 5 := by
  rw [unitBallVolumeReal_five, unitBallVolumeReal_six]
  have hpi : Real.pi < (16 : ℝ) / 5 := lt_trans pi_lt_22_div_7 (by norm_num)
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hmul := mul_lt_mul_of_pos_right hpi (sq_pos_of_pos hpipos)
  nlinarith
end Sqrt6KissingBound
