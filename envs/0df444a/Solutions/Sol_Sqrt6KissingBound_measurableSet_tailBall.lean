-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_tailBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:26:42.364266+00:00
-- url     : https://prove2.me/submissions/c4adc01e-58b8-413d-a889-27183db9b02e

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) (r : ℝ) : MeasurableSet (tailBall d r) := by
  exact measurableSet_ball.preimage (PiLp.continuous_toLp 2 _).measurable
end Sqrt6KissingBound
