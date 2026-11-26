-- Prove2me | solution 1 for Sqrt6KissingBound.volume_ball_eq_pow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:18:15.115355+00:00
-- url     : https://prove2.me/submissions/7f33ad3b-c0a2-4ce5-b6ce-0389d8ceb3ee

import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_ProfileIntegral
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
attribute [local simp] Sqrt6KissingBound.mem_tailBall



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped ENNReal Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) (r : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))) (ball 0 r) =
      ENNReal.ofReal r ^ (d + 1) * unitBallVolume (d + 1) := by
  simp [unitBallVolume, EuclideanSpace.volume_ball]
end Sqrt6KissingBound
