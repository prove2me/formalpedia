-- Prove2me | solution 1 for QEC.Locality.two_mul_packingRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:48:56.756198+00:00
-- url     : https://prove2.me/submissions/9fb14e1b-c2d8-4444-aadd-bbbc6d46da4f

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
theorem _root_.solution : 2 * packingRadius = Real.sqrt 2 / 2 := by
  rw [packingRadius]
  ring
end QEC.Locality
