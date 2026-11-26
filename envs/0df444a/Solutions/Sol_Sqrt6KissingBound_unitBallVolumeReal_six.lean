-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:14:04.95708+00:00
-- url     : https://prove2.me/submissions/4f2c34c2-8007-41dd-b364-0fcb56a8b23c

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_add_two
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_four

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution : unitBallVolumeReal 6 = Real.pi ^ 3 / 6 := by
  rw [unitBallVolumeReal_add_two 3, unitBallVolumeReal_four]
  ring
end Sqrt6KissingBound
