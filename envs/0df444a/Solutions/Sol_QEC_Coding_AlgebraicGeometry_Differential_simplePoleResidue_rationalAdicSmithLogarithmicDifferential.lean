-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicSmithLogarithmicDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:48:23.078826+00:00
-- url     : https://prove2.me/submissions/f70560de-7a1f-42a9-be96-cc31e0e58ef0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_simplePoleResidue_polynomialMatrixLogarithmicTraceDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


section
open scoped Polynomial RatFunc
namespace QEC.Coding.AlgebraicGeometry
variable {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
namespace Differential
variable {k : Type*} [Field k] [Finite k]
private theorem smith_commuting_diagonal_eq
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f) (i : Fin n) :
    LinearMap.toMatrix source source g i i =
      LinearMap.toMatrix target target g i i := by
  have hmatrix := congrArg (LinearMap.toMatrix source target) hcomm
  rw [LinearMap.toMatrix_comp source source target,
    LinearMap.toMatrix_comp source target target, hdiag] at hmatrix
  have hii := congrFun (congrFun hmatrix i) i
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hii
  exact mul_left_cancel₀ (ha i) (by simpa only [mul_comm] using hii)
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
open QEC.Coding.AlgebraicGeometry.Differential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    {N : Type*} [AddCommGroup N] [Module k[X] N] [Module.Finite k[X] N]
    {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a)
    (hcomm : f.comp g = g.comp f)
    (depth : ℕ)
    (hdepth : ∀ i,
      multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) ≤ depth) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha g) =
      GlobalPlace.rationalAdicIdealResidueEquiv p
        (primaryTorsionTrace p.asIdeal
          (cokernelEndomorphism f g hcomm) depth) := by
  have hgdiag : ∀ i, LinearMap.toMatrix source source g i i =
      LinearMap.toMatrix target target g i i :=
    smith_commuting_diagonal_eq source target a ha f g hdiag hcomm
  have hdiagonal :
      simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
            (LinearMap.toMatrix source source g) a ha) =
        simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
            (LinearMap.toMatrix target target g) a ha) := by
    rw [simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential,
      simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential]
    apply Finset.sum_congr rfl
    intro i _
    rw [hgdiag i]
  calc
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSmithLogarithmicDifferentialAtSimplePole p
          source target a ha g) =
        simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
            (LinearMap.toMatrix source source g) a ha) := by
      unfold rationalAdicSmithLogarithmicDifferentialAtSimplePole
      rw [map_add,
        simplePoleResidue_polynomialMatrixLogarithmicTraceDifferential,
        add_zero]
    _ = simplePoleResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
            (LinearMap.toMatrix target target g) a ha) := hdiagonal
    _ = GlobalPlace.rationalAdicIdealResidueEquiv p
          (primaryTorsionTrace p.asIdeal
            (cokernelEndomorphism f g hcomm) depth) :=
      (rationalAdicIdealResidueEquiv_primaryTorsionTrace_cokernel_eq_simplePoleResidue
        source target a ha f g hdiag hcomm p depth hdepth).symm
end QEC.Coding.AlgebraicGeometry.Differential
