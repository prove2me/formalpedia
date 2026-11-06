-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_trace_weighted_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:44:04.859192+00:00
-- url     : https://prove2.me/submissions/1e09fd73-5d5e-42ad-bd9d-71a7fae22985

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_mul
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



set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k₀ K : Type*} [Field k₀] [Field K] [Algebra k₀ K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation k₀ K K)
    (Gt Gs P A Ainv Q : Matrix n n K)
    (hAinvA : Ainv * A = 1)
    (hconj : Q * Gt * P = Gs) :
    Matrix.trace
        (Gt * P * Ainv * entrywiseMatrixDerivation D (A * Q)) =
      Matrix.trace (Gs * Ainv * entrywiseMatrixDerivation D A) +
        Matrix.trace ((Gt * P) * entrywiseMatrixDerivation D Q) := by
  let DA := entrywiseMatrixDerivation D A
  let DQ := entrywiseMatrixDerivation D Q
  rw [entrywiseMatrixDerivation_mul]
  change Matrix.trace (Gt * P * Ainv * (DA * Q + A * DQ)) = _
  rw [mul_add, Matrix.trace_add]
  congr 1
  · calc
      Matrix.trace (Gt * P * Ainv * (DA * Q)) =
          Matrix.trace ((Gt * P * Ainv * DA) * Q) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Q * (Gt * P * Ainv * DA)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Q * Gt * P) * Ainv * DA) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Gs * Ainv * DA) := by rw [hconj]
  · congr 1
    calc
      Gt * P * Ainv * (A * DQ) =
          (Gt * P) * (Ainv * A) * DQ := by
            simp only [Matrix.mul_assoc]
      _ = (Gt * P) * DQ := by rw [hAinvA, mul_one]
end QEC.Coding.AlgebraicGeometry
