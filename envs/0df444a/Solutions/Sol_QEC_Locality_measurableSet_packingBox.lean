-- Prove2me | solution 1 for QEC.Locality.measurableSet_packingBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:37:42.48354+00:00
-- url     : https://prove2.me/submissions/f3ebea5c-d015-4528-b781-4c50871222e6

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
theorem _root_.solution (p : ℝ × ℝ) : MeasurableSet (packingBox p) :=
  measurableSet_Ioo.prod measurableSet_Ioo
end QEC.Locality
