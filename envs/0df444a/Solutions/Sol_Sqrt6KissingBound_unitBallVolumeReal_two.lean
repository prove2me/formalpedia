-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:33.375287+00:00
-- url     : https://prove2.me/submissions/92fb738c-aa38-4d3b-9df9-67c9f1798bdf

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
theorem _root_.solution : unitBallVolumeReal 2 = Real.pi := by
  rw [unitBallVolumeReal, Measure.real, EuclideanSpace.volume_ball_fin_two]
  simp [Real.pi_pos.le]
end Sqrt6KissingBound
