-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:11:41.078348+00:00
-- url     : https://prove2.me/submissions/5297ea13-2e2b-48e2-8f79-3e8255b3406d

import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Theorems.Thm_Sqrt6KissingBound_unitBallVolumeReal_formula

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) :
    unitBallVolumeReal (d + 3) =
      (2 * Real.pi / (d + 3)) * unitBallVolumeReal (d + 1) := by
  rw [unitBallVolumeReal_formula (d + 2), unitBallVolumeReal_formula d]
  have hz : 0 < (((d + 1 : ℕ) : ℝ) / 2 + 1) := by positivity
  have hG : Real.Gamma (((d + 1 : ℕ) : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos hz).ne'
  have harg : (((d + 3 : ℕ) : ℝ) / 2 + 1) =
      (((d + 1 : ℕ) : ℝ) / 2 + 1) + 1 := by
    push_cast
    ring
  rw [harg, Real.Gamma_add_one (ne_of_gt hz)]
  rw [show d + 3 = (d + 1) + 2 by omega, pow_add, Real.sq_sqrt Real.pi_nonneg]
  field_simp [hG]
  push_cast
  ring
end Sqrt6KissingBound
