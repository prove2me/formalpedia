-- Prove2me | solution 1 for QEC.Locality.measurableSet_edgeBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:10:43.495451+00:00
-- url     : https://prove2.me/submissions/e8a03a29-4ed5-4cd0-8320-51c36cf0134d

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
theorem _root_.solution (w r : ℝ) (p : ℝ × ℝ) :
    MeasurableSet {t : AddCircle w × AddCircle w | edgeBad w r t p} := by
  rw [edgeBad_set]
  exact (measurableSet_closedBall.prod MeasurableSet.univ).union
    (MeasurableSet.univ.prod measurableSet_closedBall)
end QEC.Locality
