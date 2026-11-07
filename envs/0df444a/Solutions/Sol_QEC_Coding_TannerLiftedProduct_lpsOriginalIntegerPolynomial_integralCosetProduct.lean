-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_integralCosetProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:45:56.725534+00:00
-- url     : https://prove2.me/submissions/e9e07817-5896-41da-9580-dbea0ba9c603

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_actualCosetTaylorProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetIntegralCuspSeries_complex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralLevelCoefficientEval_complex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralCuspComplexMap_injective
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    (lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalIntegralLevelCoefficientEval N hN) =
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalCosetIntegralCuspSeries N hN x)) := by
  classical
  let := Fintype.ofFinite (LPSOriginalCuspIndex N)
  apply Polynomial.map_injective
    (lpsOriginalCuspCoefficientMap (lpsOriginalLevelPhaseRing N).val.toRingHom)
    (lpsOriginalIntegralCuspComplexMap_injective N)
  rw [Polynomial.map_map,lpsOriginalIntegralLevelCoefficientEval_complex,
    ← Polynomial.map_map,Polynomial.map_prod]
  simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    lpsOriginalCosetIntegralCuspSeries_complex]
  exact lpsOriginalIntegerPolynomial_actualCosetTaylorProduct N hN
end QEC.Coding.TannerLiftedProduct
