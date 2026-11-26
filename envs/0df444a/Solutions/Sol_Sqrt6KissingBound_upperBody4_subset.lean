-- Prove2me | solution 1 for Sqrt6KissingBound.upperBody4_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:23:13.931529+00:00
-- url     : https://prove2.me/submissions/129a87b5-6528-4f81-86f9-3b587fd60a29

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_upperProfile4_nonneg
import Theorems.Thm_Sqrt6KissingBound_upperProfile4_sq_le
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
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
private lemma s3_sq : s3_d4 ^ 2 = 3 := by norm_num [s3_d4]
private lemma upperBody4_point_mem {t : ℝ} {v : Fin 3 → ℝ}
    (hta : a_d4 < t) (ht1 : t < 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ < upperProfile4 t) :
    standardCoordinates 3 (t, v) ∈ strictCone (standardAxis 3) ∩ ball 0 1 := by
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have ht0 : 0 < t := lt_trans (by positivity : 0 < a_d4) hta
  have hg0 : 0 ≤ upperProfile4 t := upperProfile4_nonneg hta.le ht1.le
  have hrsq : r ^ 2 < upperProfile4 t ^ 2 :=
    (sq_lt_sq₀ hr0 hg0).2 (by simpa [r] using hv)
  have hcircle := upperProfile4_sq_le hta.le ht1.le
  have hrball : r ^ 2 < 1 - t ^ 2 := lt_of_lt_of_le hrsq hcircle
  have ht_sq_gt : (3 : ℝ) / 4 < t ^ 2 := by
    have ha0 : 0 ≤ a_d4 := by positivity
    have hsq := (sq_lt_sq₀ ha0 ht0.le).2 hta
    dsimp [a_d4] at hsq
    nlinarith [s3_sq]
  have hcone_sq : 3 * r ^ 2 < t ^ 2 := by nlinarith
  constructor
  · rw [standardCoordinates_mem_strictCone_iff]
    have hq : 0 ≤ t ^ 2 + r ^ 2 := by positivity
    have hleft : 0 ≤ (s3_d4 / 2) * Real.sqrt (t ^ 2 + r ^ 2) := by positivity
    apply (sq_lt_sq₀ hleft ht0.le).1
    rw [mul_pow, Real.sq_sqrt hq]
    nlinarith [s3_sq]
  · rw [standardCoordinates_mem_ball_iff]
    nlinarith
end
end Sqrt6KissingBound
end

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution : upperBody4 ⊆ strictCone (standardAxis 3) ∩ ball 0 1 := by
  intro y hy
  let p := (standardCoordinates 3).symm y
  have hp : p ∈ profileRegion 3 (Set.Ioo a_d4 1) upperProfile4 := hy
  rcases hp with ⟨ht, hv⟩
  have hpoint := upperBody4_point_mem ht.1 ht.2 hv
  simpa [p] using hpoint
end Sqrt6KissingBound
