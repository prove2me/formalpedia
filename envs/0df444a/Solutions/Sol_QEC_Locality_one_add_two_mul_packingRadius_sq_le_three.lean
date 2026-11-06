-- Prove2me | solution 1 for QEC.Locality.one_add_two_mul_packingRadius_sq_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:01:16.022597+00:00
-- url     : https://prove2.me/submissions/0083361e-f7e5-4577-990a-5c9384e713dc

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_two_mul_packingRadius

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution :
    (1 + 2 * packingRadius) ^ 2 ≤ (3 : ℝ) := by
  rw [two_mul_packingRadius]
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
end QEC.Locality
