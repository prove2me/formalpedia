-- Prove2me | solution 1 for Sqrt6KissingBound.upperBody3_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:16:57.556004+00:00
-- url     : https://prove2.me/submissions/eb899c83-3d06-4344-b275-f7cc6d195f53

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_upperProfile3_nonneg
import Theorems.Thm_Sqrt6KissingBound_upperProfile3_sq
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
private lemma s3_sq : s3_d3 ^ 2 = 3 := by norm_num [s3_d3]
private lemma a_nonneg : 0 ≤ a_d3 := by positivity
private lemma upperBody3_point_mem {t : ℝ} {v : Fin 2 → ℝ}
    (hta : a_d3 < t) (ht1 : t < 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖ < upperProfile3 t) :
    standardCoordinates 2 (t, v) ∈ strictCone (standardAxis 2) ∩ ball 0 1 := by
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have ht0 : 0 < t := lt_of_le_of_lt a_nonneg hta
  have hrsq : r ^ 2 < upperProfile3 t ^ 2 :=
    (sq_lt_sq₀ hr0 (upperProfile3_nonneg t)).2 (by simpa [r] using hv)
  have hrball : r ^ 2 < 1 - t ^ 2 := by
    rwa [upperProfile3_sq ht0.le ht1.le] at hrsq
  have ht_sq_gt : (3 : ℝ) / 4 < t ^ 2 := by
    have hsq := (sq_lt_sq₀ a_nonneg ht0.le).2 hta
    dsimp [a_d3] at hsq
    nlinarith [s3_sq]
  have hcone_sq : 3 * r ^ 2 < t ^ 2 := by nlinarith
  constructor
  · rw [standardCoordinates_mem_strictCone_iff]
    have hq : 0 ≤ t ^ 2 + r ^ 2 := by positivity
    have hleft : 0 ≤ (s3_d3 / 2) * Real.sqrt (t ^ 2 + r ^ 2) := by positivity
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
namespace Sqrt6KissingBound
theorem _root_.solution : upperBody3 ⊆ strictCone (standardAxis 2) ∩ ball 0 1 := by
  intro y hy
  let p := (standardCoordinates 2).symm y
  have hp : p ∈ profileRegion 2 (Set.Ioo a_d3 1) upperProfile3 := hy
  rcases hp with ⟨ht, hv⟩
  have hpoint := upperBody3_point_mem ht.1 ht.2 hv
  simpa [p] using hpoint
end Sqrt6KissingBound
