-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.dilation_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:03:21.500627+00:00
-- url     : https://prove2.me/submissions/48048c43-ba8a-413b-9321-6d1a9d079818

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

open ShorNonsmooth.SpaceDilation in
theorem solution {n : ℕ} (α : ℝ) (hα : 0 ≤ α) (ξ : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) (x : EuclideanSpace ℝ (Fin n)) :
    ‖dilation α ξ x‖ = Real.sqrt (‖x‖ ^ 2 + (α ^ 2 - 1) * (inner ℝ x ξ) ^ 2) := by
  have key : dilation α ξ x = x + ((α - 1) * inner ℝ x ξ) • ξ := by
    have hi : (innerSL ℝ ξ) x = inner ℝ x ξ := by
      rw [real_inner_comm]; rfl
    simp only [dilation, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, hi]
    module
  rw [key, ← Real.sqrt_sq (norm_nonneg _)]
  congr 1
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right, hξ,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring
