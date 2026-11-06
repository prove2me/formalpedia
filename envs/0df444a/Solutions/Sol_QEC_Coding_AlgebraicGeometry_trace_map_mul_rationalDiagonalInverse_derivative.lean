-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.trace_map_mul_rationalDiagonalInverse_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:39:43.243296+00:00
-- url     : https://prove2.me/submissions/d74fce8e-ee92-4bcf-8da8-aca516f9c504

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_map_polynomial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
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
variable {k : Type*} [Field k]
private theorem entrywisePolynomialDerivative_diagonal
    {n : Type*} [DecidableEq n] (a : n → k[X]) :
    entrywisePolynomialDerivative (Matrix.diagonal a) =
      Matrix.diagonal fun i => (a i).derivative := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [entrywisePolynomialDerivative_apply, Matrix.diagonal_apply_eq]
  · simp only [entrywisePolynomialDerivative_apply,
      Matrix.diagonal_apply_ne _ hij, Polynomial.derivative_zero]
namespace Differential
open FunctionFieldDifferential
variable [Finite k]
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n k[X]) (a : n → k[X]) :
    Matrix.trace
        (((algebraMap k[X] (RatFunc k)).mapMatrix R *
            rationalDiagonalMatrixInverse a) *
          entrywiseMatrixDerivation
            (RatFuncDerivation.rationalDerivation
              (k := k) (M := RatFunc k) 1)
            ((algebraMap k[X] (RatFunc k)).mapMatrix
              (Matrix.diagonal a))) =
      ∑ i, algebraMap k[X] (RatFunc k) (R i i) *
        (algebraMap k[X] (RatFunc k) (a i))⁻¹ *
          algebraMap k[X] (RatFunc k) (a i).derivative := by
  classical
  rw [entrywiseMatrixDerivation_map_polynomial,
    entrywisePolynomialDerivative_diagonal]
  unfold rationalDiagonalMatrixInverse
  simp only [RingHom.mapMatrix_apply]
  rw [
    Matrix.diagonal_map (map_zero (algebraMap k[X] (RatFunc k)))]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal,
    Matrix.map_apply]
end QEC.Coding.AlgebraicGeometry
