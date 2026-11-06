-- Prove2me | solution 1 for QEC.Locality.expanded_area_le_three_mul_area
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:37:47.46187+00:00
-- url     : https://prove2.me/submissions/ac3c4c1b-c0dc-48be-891e-841fab12c312

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_packingRadius_pos
import Theorems.Thm_QEC_Locality_one_add_two_mul_packingRadius_sq_le_three

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution
    {width height : ℝ} (hwidth : 1 ≤ width) (hheight : 1 ≤ height) :
    (width + 2 * packingRadius) * (height + 2 * packingRadius) ≤
      3 * (width * height) := by
  have hr : 0 ≤ 2 * packingRadius :=
    mul_nonneg (by norm_num) packingRadius_pos.le
  have hx : width + 2 * packingRadius ≤ (1 + 2 * packingRadius) * width := by
    nlinarith [mul_nonneg hr (sub_nonneg.2 hwidth)]
  have hy : height + 2 * packingRadius ≤ (1 + 2 * packingRadius) * height := by
    nlinarith [mul_nonneg hr (sub_nonneg.2 hheight)]
  have hlowerY0 : 0 ≤ height + 2 * packingRadius := by
    nlinarith [packingRadius_pos.le]
  have hupperX0 : 0 ≤ (1 + 2 * packingRadius) * width := by
    exact mul_nonneg (by nlinarith [packingRadius_pos.le]) (by linarith)
  calc
    _ ≤ ((1 + 2 * packingRadius) * width) *
        ((1 + 2 * packingRadius) * height) := mul_le_mul hx hy hlowerY0 hupperX0
    _ = (1 + 2 * packingRadius) ^ 2 * (width * height) := by ring
    _ ≤ 3 * (width * height) := by
      exact mul_le_mul_of_nonneg_right one_add_two_mul_packingRadius_sq_le_three
        (mul_nonneg (by linarith) (by linarith))
end QEC.Locality
