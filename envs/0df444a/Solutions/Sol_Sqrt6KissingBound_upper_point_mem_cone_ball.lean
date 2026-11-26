-- Prove2me | solution 1 for Sqrt6KissingBound.upper_point_mem_cone_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:02.5593+00:00
-- url     : https://prove2.me/submissions/dcc6adca-0aee-494a-a75e-2d8bb25effc0

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
    (hta : a_bg < t) (ht1 : t < 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖ <
      upperSlope_bg * (1 - t)) :
    standardCoordinates (k + 1) (t, v) ∈
      strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have ht0 : 0 < t := lt_trans (by positivity : 0 < a_bg) hta
  have hprof0 : 0 < upperSlope_bg * (1 - t) := by positivity
  have hrprof : r < upperSlope_bg * (1 - t) := by simpa [r] using hv
  have hconeLinear : s3_bg * (upperSlope_bg * (1 - t)) < t := by
    dsimp [a_bg, upperSlope_bg] at hta ⊢
    nlinarith [s3_sq]
  have hrs : r * s3_bg < t := by
    have hmul := mul_lt_mul_of_pos_right hrprof s3_pos
    nlinarith
  have hrs0 : 0 ≤ r * s3_bg := mul_nonneg hr0 s3_pos.le
  have hrsq : (r * s3_bg) ^ 2 < t ^ 2 :=
    (sq_lt_sq_nonneg_iff hrs0 (by positivity : 0 ≤ t)).2 hrs
  have hr_sq : 3 * r ^ 2 < t ^ 2 := by
    nlinarith [s3_sq]
  have hballLinear : upperSlope_bg ^ 2 * (1 - t) < 1 + t := by
    dsimp [a_bg, upperSlope_bg] at hta ⊢
    nlinarith [s3_sq]
  have hprof_sq : (upperSlope_bg * (1 - t)) ^ 2 < 1 - t ^ 2 := by
    have h1t : 0 < 1 - t := by linarith
    have hmul := mul_lt_mul_of_pos_right hballLinear h1t
    nlinarith
  have hr_sq_ball : r ^ 2 < 1 - t ^ 2 := by
    have hprof_nonneg : 0 ≤ upperSlope_bg * (1 - t) := hprof0.le
    have hsq := (sq_lt_sq_nonneg_iff hr0 hprof_nonneg).2 hrprof
    nlinarith
  constructor
  · rw [standardCoordinates_mem_strictCone_iff]
    have hq : 0 ≤ t ^ 2 + r ^ 2 := by positivity
    have hleft : 0 ≤ (s3_bg / 2) * Real.sqrt (t ^ 2 + r ^ 2) := by positivity
    apply (sq_lt_sq_nonneg_iff hleft (by positivity : 0 ≤ t)).1
    rw [mul_pow, Real.sq_sqrt hq]
    nlinarith [s3_sq]
  · rw [standardCoordinates_mem_ball_iff]
    nlinarith
end Sqrt6KissingBound
