-- Prove2me | solution 1 for QEC.Locality.average_const_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:36:52.637204+00:00
-- url     : https://prove2.me/submissions/adb12fd2-d3f1-4695-b3a3-2d51345d51d8

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
theorem _root_.solution {a : Type*} [MeasurableSpace a]
    (mu : Measure a) (f g : a → ℝ) (A B : ℝ)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    (⨍ x, B * f x + A * g x ∂mu) =
      B * (⨍ x, f x ∂mu) + A * (⨍ x, g x ∂mu) := by
  rw [MeasureTheory.average_eq', MeasureTheory.average_eq', MeasureTheory.average_eq',
    MeasureTheory.integral_add (hf.to_average.const_mul B) (hg.to_average.const_mul A),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
end QEC.Locality
