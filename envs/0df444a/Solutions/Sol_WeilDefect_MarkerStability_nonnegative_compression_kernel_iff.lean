-- Prove2me | solution 1 for WeilDefect.MarkerStability.nonnegative_compression_kernel_iff
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T18:47:21.797711+00:00
-- url     : https://prove2.me/submissions/2f047fc7-cefd-4267-b329-020700f3084a

import Definitions.Def_WeilMarker_regularized_cost
set_option autoImplicit false
open scoped InnerProductSpace ComplexOrder
noncomputable section
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem neutral_inner_zero (A : H →L[ℂ] H)
    (hA : 0 ≤ A) (x : H) : RCLike.re ⟪A x, x⟫_ℂ = 0 ↔ A x = 0 := by
  let B := CFC.sqrt A
  have hB : B.adjoint = B := by
    exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hBB : B ∘L B = A := CFC.sqrt_mul_sqrt_self A hA
  have he := B.adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [hB] at he
  have he' : ‖B x‖ ^ 2 = RCLike.re ⟪A x, x⟫_ℂ := by
    simpa only [← ContinuousLinearMap.comp_apply, hBB] using he
  constructor
  · intro hx
    have hz : B x = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (B x)])
    rw [← hBB, ContinuousLinearMap.comp_apply, hz, map_zero]
  · intro hx
    simp [hx]

theorem solution (A : K →L[ℂ] K) (hA : 0 ≤ A)
    (U : H →L[ℂ] K) (x : H) :
    (U.adjoint ∘L A ∘L U) x = 0 ↔ A (U x) = 0 := by
  constructor
  · intro hx
    apply (neutral_inner_zero A hA (U x)).mp
    have he : RCLike.re ⟪(U.adjoint ∘L A ∘L U) x, x⟫_ℂ =
        RCLike.re ⟪A (U x), U x⟫_ℂ := by
      simp only [ContinuousLinearMap.comp_apply, U.adjoint_inner_left]
    rw [← he, hx]
    simp
  · intro hx
    simp only [ContinuousLinearMap.comp_apply, hx, map_zero]

