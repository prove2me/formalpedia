-- Prove2me | solution 1 for UnderstandingML.min_norm_separates
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T05:08:45.68976+00:00
-- url     : https://prove2.me/submissions/4c09ad26-83fa-48b6-9871-514ac7cd7e97

import Definitions.Def_UnderstandingML_Compression

open MeasureTheory
open scoped InnerProductSpace

theorem solution {d m : ℕ} (v : Fin m → UnderstandingML.Vec d) (w : UnderstandingML.Vec d)
    (hw : w ∈ convexHull ℝ (Set.range v))
    (hmin : ∀ u ∈ convexHull ℝ (Set.range v), ‖w‖ ≤ ‖u‖)
    (h0 : (0 : UnderstandingML.Vec d) ∉ convexHull ℝ (Set.range v)) (i : Fin m) :
    0 < ⟪w, v i⟫_ℝ := by
  by_contra hneg
  push_neg at hneg
  have hw0 : w ≠ 0 := fun h ↦ h0 (h ▸ hw)
  have ha : 0 < ‖w‖ ^ 2 := by positivity
  set x := v i with hx
  have hxmem : x ∈ convexHull ℝ (Set.range v) := subset_convexHull ℝ _ ⟨i, rfl⟩
  -- key quantities
  have hp : ⟪w, x - w⟫_ℝ ≤ -‖w‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]; linarith
  have hc : ‖w‖ ^ 2 ≤ ‖x - w‖ ^ 2 := by
    have := norm_sub_sq_real x w
    rw [real_inner_comm] at this
    nlinarith [sq_nonneg ‖x‖]
  have hcpos : 0 < ‖x - w‖ ^ 2 := lt_of_lt_of_le ha hc
  set t : ℝ := ‖w‖ ^ 2 / ‖x - w‖ ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := (div_le_one hcpos).2 hc
  have htc : t * ‖x - w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [ht]; exact div_mul_cancel₀ _ hcpos.ne'
  have htpos : 0 < t := by positivity
  set u := w + t • (x - w) with hu
  have humem : u ∈ convexHull ℝ (Set.range v) := by
    have hconv := convex_convexHull ℝ (Set.range v)
    have := hconv hw hxmem (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
    convert this using 1
    rw [hu, smul_sub]
    module
  have hnorm : ‖u‖ ^ 2 = ‖w‖ ^ 2 + 2 * t * ⟪w, x - w⟫_ℝ + t ^ 2 * ‖x - w‖ ^ 2 := by
    rw [hu, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  have hlt : ‖u‖ ^ 2 < ‖w‖ ^ 2 := by
    rw [hnorm]
    have : t ^ 2 * ‖x - w‖ ^ 2 = t * ‖w‖ ^ 2 := by rw [pow_two, mul_assoc, htc]
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : (0:ℝ) ≤ 2 * t)]
  have := hmin u humem
  nlinarith [norm_nonneg u, norm_nonneg w]
