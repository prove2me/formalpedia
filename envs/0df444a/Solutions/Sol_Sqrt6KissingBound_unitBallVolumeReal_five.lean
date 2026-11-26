-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:13:08.322149+00:00
-- url     : https://prove2.me/submissions/169024ca-b0b6-4f3c-bd07-b2499e31a29b

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_add_two
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_three

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution : unitBallVolumeReal 5 = 8 * Real.pi ^ 2 / 15 := by
  rw [unitBallVolumeReal_add_two 2, unitBallVolumeReal_three]
  ring
end Sqrt6KissingBound
