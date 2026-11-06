-- Prove2me | solution 1 for QEC.Locality.measure_vertexBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:37:35.034201+00:00
-- url     : https://prove2.me/submissions/a0c2f131-3e79-4d93-a6bd-30a66dccfe39

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_vertexBad_set

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution (w r : ℝ) [Fact (0 < w)] (p : ℝ × ℝ) :
    volume {t : AddCircle w × AddCircle w | vertexBad w r t p} =
      ENNReal.ofReal (min w (2 * r)) ^ 2 := by
  rw [vertexBad_set, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Measure.prod_prod, AddCircle.volume_closedBall,
    AddCircle.volume_closedBall, pow_two]
end QEC.Locality
