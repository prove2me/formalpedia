-- Prove2me | solution 1 for Sqrt6KissingBound.lower_point_mem_cone_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:18:59.257172+00:00
-- url     : https://prove2.me/submissions/9dc8d91a-2893-4aa6-9967-dfb9f258e612

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
import Theorems.Thm_Sqrt6KissingBound_standardCoordinates_mem_ball_iff
import Theorems.Thm_Sqrt6KissingBound_standardCoordinates_mem_strictCone_iff
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis


section
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
private lemma s3_pos : 0 < s3_bg := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3_bg ^ 2 = 3 := by norm_num [s3_bg]
private lemma sq_lt_sq_nonneg_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 < y ^ 2 ↔ x < y := by
  constructor
  · intro hsq
    by_contra hnot
    have hyx : y ≤ x := le_of_not_gt hnot
    have hprod : 0 ≤ (x - y) * (x + y) :=
      mul_nonneg (sub_nonneg.mpr hyx) (add_nonneg hx hy)
    nlinarith
  · intro hxy
    have hypos : 0 < y := lt_of_le_of_lt hx hxy
    have hprod : 0 < (y - x) * (y + x) :=
      mul_pos (sub_pos.mpr hxy) (add_pos_of_pos_of_nonneg hypos hx)
    nlinarith
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) {t : ℝ} {v : Fin (k + 1) → ℝ}
    (ht0 : 0 < t) (hta : t < a_bg)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖ < t / s3_bg) :
    standardCoordinates (k + 1) (t, v) ∈
      strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrs : r * s3_bg < t := (lt_div_iff₀ s3_pos).mp (by simpa [r] using hv)
  have hrs0 : 0 ≤ r * s3_bg := mul_nonneg hr0 s3_pos.le
  have hrsq : (r * s3_bg) ^ 2 < t ^ 2 :=
    (sq_lt_sq_nonneg_iff hrs0 ht0.le).2 hrs
  have hr_sq : 3 * r ^ 2 < t ^ 2 := by
    nlinarith [s3_sq]
  have ht_sq : t ^ 2 < (3 : ℝ) / 4 := by
    have ha0 : 0 ≤ a_bg := by positivity
    have hsq := (sq_lt_sq_nonneg_iff ht0.le ha0).2 hta
    dsimp [a_bg] at hsq
    nlinarith [s3_sq]
  constructor
  · rw [standardCoordinates_mem_strictCone_iff]
    have hq : 0 ≤ t ^ 2 + r ^ 2 := by positivity
    have hleft : 0 ≤ (s3_bg / 2) * Real.sqrt (t ^ 2 + r ^ 2) := by positivity
    apply (sq_lt_sq_nonneg_iff hleft ht0.le).1
    rw [mul_pow, Real.sq_sqrt hq]
    nlinarith [s3_sq]
  · rw [standardCoordinates_mem_ball_iff]
    nlinarith
end Sqrt6KissingBound
