-- Prove2me | solution 1 for aeval_C_star_eval_center_eq_crouzeixPolynomialAuxiliaryOperator_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:53.343245+00:00
-- url     : https://prove2.me/submissions/393b566f-ea51-48f0-9cc7-00782c8d543d

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    Polynomial.aeval A
        (Polynomial.C (star (Polynomial.eval c p))) =
      crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R hR) p := by
  rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  symm
  simpa using
    (crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
      A c hA p)
