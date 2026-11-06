-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.exists_smith_bases_toMatrix_eq_diagonal_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:22.350643+00:00
-- url     : https://prove2.me/submissions/fc6522ff-5062-4cce-9825-d5043a272a8d

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_bases_toMatrix_eq_diagonal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Module
variable {R M : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {n : ℕ}
    (b : Basis (Fin n) R M) (f g : M →ₗ[R] M)
    (hf : Function.Injective f) (hcomm : f.comp g = g.comp f) :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
          ∀ i, LinearMap.toMatrix source source g i i =
            LinearMap.toMatrix target target g i i := by
  classical
  obtain ⟨source, target, a, ha, hfdiag⟩ :=
    exists_smith_bases_toMatrix_eq_diagonal b f hf
  refine ⟨source, target, a, ha, hfdiag, ?_⟩
  intro i
  have hmatrix := congrArg (LinearMap.toMatrix source target) hcomm
  rw [LinearMap.toMatrix_comp source source target,
    LinearMap.toMatrix_comp source target target, hfdiag] at hmatrix
  have hii := congrFun (congrFun hmatrix i) i
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hii
  exact mul_left_cancel₀ (ha i) (by simpa only [mul_comm] using hii)
end QEC.Coding.AlgebraicGeometry
