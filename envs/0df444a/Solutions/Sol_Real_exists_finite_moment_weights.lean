-- Prove2me | solution 1 for Real.exists_finite_moment_weights
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T09:12:57.098261+00:00
-- url     : https://prove2.me/submissions/67cc87a3-1ad2-4d11-8fff-bf134426508e

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
set_option autoImplicit false

theorem solution (N : ℕ) (v : Fin N → ℝ) (hv : Function.Injective v) (a : ℝ) :
    ∃ c : Fin N → ℝ, ∀ r : Fin N, ∑ j : Fin N, c j * v j ^ (r : ℕ) = a ^ (r : ℕ) := by
  classical
  have hd : (Matrix.vandermonde v).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hu : IsUnit (Matrix.vandermonde v).transpose :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) (fun r : Fin N => a ^ (r : ℕ))
  refine ⟨c, fun r => ?_⟩
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.vandermonde_apply, mul_comm] using congrFun hc r
