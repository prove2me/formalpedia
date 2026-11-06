-- Prove2me | solution 1 for QEC.Locality.measurableSet_vertexBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:48:36.722392+00:00
-- url     : https://prove2.me/submissions/bc29fd02-0c5e-40c0-8033-ee146ccfc589

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution (w r : ℝ) (p : ℝ × ℝ) :
    MeasurableSet {t : AddCircle w × AddCircle w | vertexBad w r t p} := by
  change MeasurableSet (closedBall (phase w p).1 r ×ˢ closedBall (phase w p).2 r)
  exact measurableSet_closedBall.prod measurableSet_closedBall
end QEC.Locality
