-- Prove2me | solution 1 for ShorNonsmooth.Ellipsoid.dilation_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:39:58.072835+00:00
-- url     : https://prove2.me/submissions/bf962295-bb00-4aff-a242-d60a76e9b993

import Mathlib
import Definitions.Def_ShorNonsmooth_Ellipsoid_EllipsoidMethod

set_option autoImplicit false

open ShorNonsmooth.Ellipsoid in
theorem dilation_apply_aux {n : ℕ} (α : ℝ) (ξ x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (dilationMatrix α ξ) x = x + ((α - 1) * inner ℝ x ξ) • ξ := by
  ext i
  simp only [dilationMatrix, Matrix.toEuclideanLin_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, PiLp.toLp_apply]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

open ShorNonsmooth.Ellipsoid in
theorem solution {n : ℕ} (α : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ = 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin (dilationMatrix α ξ) x‖ =
      Real.sqrt (‖x‖ ^ 2 + (α ^ 2 - 1) * (inner ℝ x ξ) ^ 2) := by
  rw [dilation_apply_aux, ← Real.sqrt_sq (norm_nonneg (x + ((α - 1) * inner ℝ x ξ) • ξ))]
  congr 1
  rw [@norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs, hξ]
  ring
