-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_six_gt_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:35.578796+00:00
-- url     : https://prove2.me/submissions/7cf7ab2f-97b9-414e-96dd-2b7dfbdb41e3

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_six
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_seven

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution : unitBallVolumeReal 7 < unitBallVolumeReal 6 := by
  rw [unitBallVolumeReal_six, unitBallVolumeReal_seven]
  have hpipos : 0 < Real.pi := Real.pi_pos
  nlinarith [pow_pos hpipos 3]
end Sqrt6KissingBound
