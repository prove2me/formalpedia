-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:31.042796+00:00
-- url     : https://prove2.me/submissions/10f8eb68-7f68-4ac8-ac94-5eb390a4c0ff

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
attribute [local simp] Sqrt6KissingBound.mem_tailBall



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution : unitBallVolumeReal 3 = 4 * Real.pi / 3 := by
  rw [unitBallVolumeReal, Measure.real, EuclideanSpace.volume_ball_fin_three]
  simp [Real.pi_pos.le]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring
end Sqrt6KissingBound
