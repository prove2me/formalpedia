-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLevelJPolynomialEval_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:39:34.150279+00:00
-- url     : https://prove2.me/submissions/72cd222a-27e2-4030-b43f-39fa6e7935cd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspJNumerator_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
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
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldCuspSeries_domain
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (K : Type*) [Field K] (N : ℕ) (hN : 0 < N) :
    Function.Injective (lpsOriginalFieldLevelJPolynomialEval K N hN) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  have hF : PowerSeries.constantCoeff
      (PowerSeries.expand N hN.ne' (lpsOriginalCuspJNumerator K)) = 1 := by
    rw [PowerSeries.constantCoeff_expand,lpsOriginalCuspJNumerator_constant]
  apply (lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
    (PowerSeries.expand N hN.ne' (lpsOriginalCuspJNumerator K)) hF N hN P).mp
  simpa only [lpsOriginalFieldLevelJPolynomialEval,Polynomial.coe_eval₂RingHom,
    lpsOriginalCuspJWidth] using hP
end QEC.Coding.TannerLiftedProduct
