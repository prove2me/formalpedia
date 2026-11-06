-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.exists_smith_bases_toMatrix_eq_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:32.273765+00:00
-- url     : https://prove2.me/submissions/c6d5fb96-403a-436d-a4d8-41d5f6b71d81

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Module
variable {R M : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {n : ℕ}
    (b : Basis (Fin n) R M) (f : M →ₗ[R] M)
    (hf : Function.Injective f) :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a := by
  classical
  let N : Submodule R M := LinearMap.range f
  have hfinrank : Module.finrank R N = Module.finrank R M := by
    exact LinearMap.finrank_range_of_inj hf
  let target : Basis (Fin n) R M :=
    N.smithNormalFormTopBasis b hfinrank
  let rangeBasis : Basis (Fin n) R N :=
    N.smithNormalFormBotBasis b hfinrank
  let a : Fin n → R := N.smithNormalFormCoeffs b hfinrank
  let rangeEquiv : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  let source : Basis (Fin n) R M := rangeBasis.map rangeEquiv.symm
  have hsource (i : Fin n) : f (source i) = a i • target i := by
    calc
      f (source i) = (rangeBasis i : M) := by
        change f ((LinearEquiv.ofInjective f hf).symm (rangeBasis i)) =
          (rangeBasis i : M)
        exact LinearEquiv.ofInjective_symm_apply f (rangeBasis i)
      _ = a i • target i := by
        exact N.smithNormalFormBotBasis_def b hfinrank i
  refine ⟨source, target, a, ?_, ?_⟩
  · intro i
    exact N.smithNormalFormCoeffs_ne_zero b hfinrank i
  · ext i j
    rw [LinearMap.toMatrix_apply, hsource, map_smul, Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
end QEC.Coding.AlgebraicGeometry
