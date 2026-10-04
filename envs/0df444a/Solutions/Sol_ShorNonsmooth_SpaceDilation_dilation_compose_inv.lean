-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.dilation_compose_inv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:38:53.885627+00:00
-- url     : https://prove2.me/submissions/693d43eb-b22a-4014-84e2-c1beca95c32c

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation in
theorem solution {n : ℕ} (a : ℝ) (ha : a ≠ 0) (ξ : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) : dilation a ξ ∘ dilation (1 / a) ξ = ContinuousLinearMap.id ℝ _ := by
  funext x
  have hξξ : inner ℝ ξ ξ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hξ]; norm_num
  simp only [Function.comp_apply, dilation, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply]
  simp only [inner_add_right, inner_smul_right, inner_sub_right, hξξ]
  set c : ℝ := inner ℝ ξ x
  have h2 : a * (1 / a * c) = c := by field_simp
  simp only [smul_smul, mul_one, sub_self, add_zero, h2]
  module
