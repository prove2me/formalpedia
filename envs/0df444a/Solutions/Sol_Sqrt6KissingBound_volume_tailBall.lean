-- Prove2me | solution 1 for Sqrt6KissingBound.volume_tailBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:18:08.925672+00:00
-- url     : https://prove2.me/submissions/1fcba419-8a7a-4e54-a809-8df9c7922e24

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) (r : ℝ) :
    (volume : Measure (Fin d → ℝ)) (tailBall d r) =
      (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 r) := by
  exact (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_ball.nullMeasurableSet
end Sqrt6KissingBound
