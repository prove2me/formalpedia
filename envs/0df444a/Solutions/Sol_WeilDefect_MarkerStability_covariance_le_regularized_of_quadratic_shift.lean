-- Prove2me | solution 1 for WeilDefect.MarkerStability.covariance_le_regularized_of_quadratic_shift
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T20:20:34.873826+00:00
-- url     : https://prove2.me/submissions/16e9e303-ef9a-4564-b7d6-7904ae993894

import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A proved quadratic lower bound yields covariance order above that shift.
There is no assertion about smaller positive regularizations. -/
theorem solution (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (N : K →L[ℂ] H) (k ε : ℝ) (hkε : k ≤ ε)
    (hbound : ∀ x : H, -k * ‖x‖ ^ 2 ≤
      RCLike.re ⟪A x, x⟫_ℂ - ‖N.adjoint x‖ ^ 2) :
    N ∘L N.adjoint ≤ A + ε • 1 := by
  change (A + ε • 1 - N ∘L N.adjoint).IsPositive
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(hA.add ((IsSelfAdjoint.all ε).smul
    (ContinuousLinearMap.isPositive_one).isSelfAdjoint)).sub
      (ContinuousLinearMap.isPositive_self_comp_adjoint N).isSelfAdjoint, ?_⟩
  intro x
  have he := N.adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint] at he
  have hr : RCLike.re ⟪(ε • (1 : H →L[ℂ] H)) x, x⟫_ℂ = ε * ‖x‖ ^ 2 := by
    letI := InnerProductSpace.rclikeToReal ℂ H
    simp only [smul_apply, one_apply_eq_self]
    rw [← real_inner_eq_re_inner ℂ]
    exact (real_inner_smul_left x x ε).trans
      (congrArg (fun r : ℝ => ε * r) (real_inner_self_eq_norm_sq x))
  change 0 ≤ RCLike.re ⟪(A + ε • 1 - N ∘L N.adjoint) x, x⟫_ℂ
  simp only [sub_apply, add_apply, inner_sub_left, inner_add_left, map_sub, map_add]
  rw [hr, ← he]
  nlinarith [hbound x, mul_le_mul_of_nonneg_right hkε (sq_nonneg ‖x‖)]


