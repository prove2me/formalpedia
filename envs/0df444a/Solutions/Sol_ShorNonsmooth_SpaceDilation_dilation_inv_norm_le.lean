-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.dilation_inv_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T07:47:19.676622+00:00
-- url     : https://prove2.me/submissions/6119c42a-dd27-4e23-8a73-b8b5a87d4ff5

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation in
theorem solution {n : ℕ} (a : ℝ) (ha : 1 ≤ a)
    (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖dilation (1 / a) ξ v‖ ≤ ‖v‖ := by
  set c : ℝ := inner ℝ ξ v with hc
  set t : ℝ := 1 / a - 1 with ht
  have hD : dilation (1 / a) ξ v = v + (t * c) • ξ := by
    simp only [dilation, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply]
    rw [← hc, ht]
    module
  have hinner : inner ℝ v ξ = c := by rw [hc, real_inner_comm]
  have hsq : ‖dilation (1 / a) ξ v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hD, norm_add_sq_real, inner_smul_right, hinner, norm_smul, hξ, mul_one,
      Real.norm_eq_abs, sq_abs]
    have hapos : 0 < a := by linarith
    have h1 : 0 < 1 / a := by positivity
    have h2 : 1 / a ≤ 1 := by rw [div_le_one hapos]; exact ha
    have h3 : (t + 1) ^ 2 ≤ 1 := by
      rw [ht]; nlinarith
    have h4 : c ^ 2 * ((t + 1) ^ 2 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) (by linarith)
    nlinarith [h4]
  have hn1 := norm_nonneg (dilation (1 / a) ξ v)
  have hn2 := norm_nonneg v
  nlinarith [hsq, hn1, hn2]
