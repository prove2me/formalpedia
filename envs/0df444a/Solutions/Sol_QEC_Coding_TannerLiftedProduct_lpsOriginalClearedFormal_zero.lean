-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedFormal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:29:58.889416+00:00
-- url     : https://prove2.me/submissions/820a3ff2-d805-4c06-94da-db15d3af504b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_C_mul_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero_iff_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_zero_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) :
    lpsOriginalClearedFormal N (Nat.ne_of_gt hN) (lpsOriginalClearingBound N P) P=0 := by
  have hz := (lpsOriginalTaylorSeries_zero_iff_germ
    (lpsOriginalClearedCusp_analytic N (Nat.ne_of_gt hN) _ P)).mpr
      (lpsOriginalClearedCusp_zero_germ N hN P hroot)
  rw [lpsOriginalClearedCusp_taylor] at hz
  have h := congrArg lpsOriginalRationalSeriesRetraction hz
  simpa only [lpsOriginalRationalSeriesRetraction_sum,
    lpsOriginalRationalSeriesRetraction_C_mul_map,lpsOriginalRationalSeriesRetraction_zero,
    lpsOriginalClearedFormal] using h
end QEC.Coding.TannerLiftedProduct
