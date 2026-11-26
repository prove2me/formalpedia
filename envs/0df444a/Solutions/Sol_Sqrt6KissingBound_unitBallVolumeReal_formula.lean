-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:10:45.056399+00:00
-- url     : https://prove2.me/submissions/c14f163d-eef4-4c97-9168-2ba54a43ed48

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
theorem _root_.solution (d : ℕ) :
    unitBallVolumeReal (d + 1) =
      Real.sqrt Real.pi ^ (d + 1) /
        Real.Gamma (((d + 1 : ℕ) : ℝ) / 2 + 1) := by
  rw [unitBallVolumeReal, Measure.real, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal]
  positivity
end Sqrt6KissingBound
