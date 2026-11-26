-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_seven
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:18:23.867586+00:00
-- url     : https://prove2.me/submissions/b86fa56b-915f-4e3b-a26f-fd23395934d8

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_add_two
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_five

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution : unitBallVolumeReal 7 = 16 * Real.pi ^ 3 / 105 := by
  rw [unitBallVolumeReal_add_two 4, unitBallVolumeReal_five]
  ring
end Sqrt6KissingBound
