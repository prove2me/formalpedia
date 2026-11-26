-- Prove2me | solution 1 for Sqrt6KissingBound.unitBallVolumeReal_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:18:19.561798+00:00
-- url     : https://prove2.me/submissions/d8f13b8f-fbfc-453a-9449-3c788185cbd7

import Definitions.Def_Sqrt6KissingBound_ProfileIntegral
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped ENNReal Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) : 0 < unitBallVolumeReal (d + 1) := by
  exact ENNReal.toReal_pos
    (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin (d + 1)))) 0
      zero_lt_one).ne'
    measure_ball_lt_top.ne
end Sqrt6KissingBound
