-- Prove2me | solution 1 for QEC.Locality.measure_edgeBad_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:36:51.771083+00:00
-- url     : https://prove2.me/submissions/54b0a0dd-e86d-4721-a082-b9d69ac85796

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_edgeBad_set

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution (w r : ℝ) [Fact (0 < w)] (p : ℝ × ℝ) :
    volume {t : AddCircle w × AddCircle w | edgeBad w r t p} ≤
      2 * (ENNReal.ofReal (min w (2 * r)) * ENNReal.ofReal w) := by
  rw [edgeBad_set, MeasureTheory.Measure.volume_eq_prod]
  calc
    _ ≤ volume (closedBall (phase w p).1 r ×ˢ (Set.univ : Set (AddCircle w))) +
        volume ((Set.univ : Set (AddCircle w)) ×ˢ closedBall (phase w p).2 r) :=
      measure_union_le _ _
    _ = _ := by
      change (volume.prod volume) (closedBall (phase w p).1 r ×ˢ Set.univ) +
        (volume.prod volume) (Set.univ ×ˢ closedBall (phase w p).2 r) = _
      rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.prod_prod,
        AddCircle.volume_closedBall, AddCircle.volume_closedBall,
        AddCircle.measure_univ]
      ring
end QEC.Locality
