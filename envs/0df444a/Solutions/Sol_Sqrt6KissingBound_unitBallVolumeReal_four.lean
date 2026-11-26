-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:12:57.449957+00:00
-- url     : https://prove2.me/submissions/e31cb028-9858-4fcb-91d1-de82ead3e451

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_add_two
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_two

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution : unitBallVolumeReal 4 = Real.pi ^ 2 / 2 := by
  rw [unitBallVolumeReal_add_two 1, unitBallVolumeReal_two]
  ring
end Sqrt6KissingBound
