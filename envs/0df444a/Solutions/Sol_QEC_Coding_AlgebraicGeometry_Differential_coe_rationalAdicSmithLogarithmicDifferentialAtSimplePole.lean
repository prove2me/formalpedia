-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSmithLogarithmicDifferentialAtSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:55.468684+00:00
-- url     : https://prove2.me/submissions/91f0e443-a181-4959-b198-b943e2781df8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_trace_weighted_diagonal_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_coe_polynomialMatrixLogarithmicTraceDifferentialAtSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
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
private theorem rationalDiagonalMatrixInverse_mul_map_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (a : n → k[X]) (ha : ∀ i, a i ≠ 0) :
    rationalDiagonalMatrixInverse a *
        (algebraMap k[X] (RatFunc k)).mapMatrix (Matrix.diagonal a) = 1 := by
  classical
  unfold rationalDiagonalMatrixInverse
  simp only [RingHom.mapMatrix_apply]
  rw [Matrix.diagonal_map (map_zero (algebraMap k[X] (RatFunc k))),
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    have hai : algebraMap k[X] (RatFunc k) (a i) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (ha i)
    simp [Matrix.one_apply, hai]
  · simp [Matrix.one_apply, hij]
private theorem smith_target_matrix_eq_diagonal_mul_change
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (f : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    LinearMap.toMatrix target target f =
      Matrix.diagonal a * source.toMatrix target := by
  rw [← hdiag]
  symm
  exact linearMap_toMatrix_mul_basis_toMatrix target source target f
private theorem smith_change_conjugates_target_matrix
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (source target : Module.Basis (Fin n) k[X] N)
    (g : N →ₗ[k[X]] N) :
    source.toMatrix target * LinearMap.toMatrix target target g *
        target.toMatrix source =
      LinearMap.toMatrix source source g := by
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    source target source target g
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
    {N : Type*} [AddCommGroup N] [Module k[X] N]
    {n : ℕ} (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X] N)
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (f g : N →ₗ[k[X]] N)
    (hdiag : LinearMap.toMatrix source target f = Matrix.diagonal a) :
    ((rationalAdicSmithLogarithmicDifferentialAtSimplePole p
      source target a ha g :
        simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
          Differential k (RatFunc k)) =
      Matrix.trace
          (((algebraMap k[X] (RatFunc k)).mapMatrix
                (LinearMap.toMatrix target target g) *
              (algebraMap k[X] (RatFunc k)).mapMatrix
                (target.toMatrix source)) *
            rationalDiagonalMatrixInverse a *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix
                (LinearMap.toMatrix target target f))) •
        FunctionFieldDifferential.functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k) := by
  classical
  let m := algebraMap k[X] (RatFunc k)
  let Gt := m.mapMatrix (LinearMap.toMatrix target target g)
  let Gs := m.mapMatrix (LinearMap.toMatrix source source g)
  let P := m.mapMatrix (target.toMatrix source)
  let A := m.mapMatrix (Matrix.diagonal a)
  let Ainv := rationalDiagonalMatrixInverse a
  let Q := m.mapMatrix (source.toMatrix target)
  let D := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  have hAinvA : Ainv * A = 1 := by
    exact rationalDiagonalMatrixInverse_mul_map_diagonal a ha
  have hconj : Q * Gt * P = Gs := by
    have h := congrArg m.mapMatrix
      (smith_change_conjugates_target_matrix source target g)
    simpa only [map_mul] using h
  have hfmatrix : m.mapMatrix (LinearMap.toMatrix target target f) = A * Q := by
    have h := congrArg m.mapMatrix
      (smith_target_matrix_eq_diagonal_mul_change source target a f hdiag)
    simpa only [map_mul] using h
  unfold rationalAdicSmithLogarithmicDifferentialAtSimplePole
  change (simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)).subtype
      (_ + _) = _
  rw [map_add]
  have hdiagCoe :=
    coe_rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
      (LinearMap.toMatrix source source g) a ha
  have hpolyCoe :=
    coe_polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p
      (LinearMap.toMatrix target target g * target.toMatrix source)
      (source.toMatrix target)
  change (simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p)).subtype
        (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p
          (LinearMap.toMatrix source source g) a ha) = _ at hdiagCoe
  change (simplePoleDifferentialLattice
      (GlobalPlace.rationalAdic p)).subtype
        (polynomialMatrixLogarithmicTraceDifferentialAtSimplePole p
          (LinearMap.toMatrix target target g * target.toMatrix source)
          (source.toMatrix target)) = _ at hpolyCoe
  rw [hdiagCoe, hpolyCoe]
  rw [← add_smul]
  congr 1
  rw [map_mul]
  change Matrix.trace (Gs * Ainv * entrywiseMatrixDerivation D A) +
      Matrix.trace ((Gt * P) * entrywiseMatrixDerivation D Q) =
    Matrix.trace (Gt * P * Ainv *
      entrywiseMatrixDerivation D
        (m.mapMatrix (LinearMap.toMatrix target target f)))
  rw [hfmatrix]
  exact (entrywiseMatrixDerivation_trace_weighted_diagonal_mul
    D Gt Gs P A Ainv Q hAinvA hconj).symm
end QEC.Coding.AlgebraicGeometry.Differential
