-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaQSeries_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:50:43.208497+00:00
-- url     : https://prove2.me/submissions/b6e8c7a2-e7ba-41ed-8933-2a092bee4354

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4QSeries_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE6QSeries_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDiscriminant_qExpansion_formula
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
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.map (algebraMap ℚ ℂ) lpsOriginalDeltaQSeries=
      qExpansion 1 ModularForm.discriminant := by
  simp only [lpsOriginalDeltaQSeries,map_mul,PowerSeries.map_C,map_sub,map_pow,
    lpsOriginalE4QSeries_map,lpsOriginalE6QSeries_map,
    lpsOriginalDiscriminant_qExpansion_formula,PowerSeries.smul_eq_C_mul]
  norm_num
end QEC.Coding.TannerLiftedProduct
