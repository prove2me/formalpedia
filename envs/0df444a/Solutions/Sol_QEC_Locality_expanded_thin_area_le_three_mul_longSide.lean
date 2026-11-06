-- Prove2me | solution 1 for QEC.Locality.expanded_thin_area_le_three_mul_longSide
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:43:25.55919+00:00
-- url     : https://prove2.me/submissions/5c1eb595-311f-423e-aeef-c7237ac3d76a

import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Theorems.Thm_QEC_Locality_packingRadius_pos
import Theorems.Thm_QEC_Locality_one_add_two_mul_packingRadius_sq_le_three

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality

theorem solution
    {longSide thinSide : ℝ} (hlong : 1 ≤ longSide)
    (hthin0 : 0 ≤ thinSide) (hthin1 : thinSide ≤ 1) :
    (longSide + 2 * packingRadius) * (thinSide + 2 * packingRadius) ≤
      3 * longSide := by
  have hr : 0 ≤ 2 * packingRadius :=
    mul_nonneg (by norm_num) packingRadius_pos.le
  have hx : longSide + 2 * packingRadius ≤
      (1 + 2 * packingRadius) * longSide := by
    nlinarith [mul_nonneg hr (sub_nonneg.2 hlong)]
  have hy : thinSide + 2 * packingRadius ≤ 1 + 2 * packingRadius := by linarith
  have hlowerY0 : 0 ≤ thinSide + 2 * packingRadius := by
    nlinarith [packingRadius_pos.le]
  have hupperX0 : 0 ≤ (1 + 2 * packingRadius) * longSide := by
    exact mul_nonneg (by nlinarith [packingRadius_pos.le]) (by linarith)
  calc
    _ ≤ ((1 + 2 * packingRadius) * longSide) *
        (1 + 2 * packingRadius) := mul_le_mul hx hy hlowerY0 hupperX0
    _ = (1 + 2 * packingRadius) ^ 2 * longSide := by ring
    _ ≤ 3 * longSide := by
      exact mul_le_mul_of_nonneg_right one_add_two_mul_packingRadius_sq_le_three
        (by linarith)
