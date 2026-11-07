-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicPrimeCoefficientEval_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:41:09.695186+00:00
-- url     : https://prove2.me/submissions/75f8c57f-0fc6-4f13-b538-63a7b46333e3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_jWidth
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p)).comp
      (lpsOriginalCyclotomicPrimeCoefficientEval p)=
    lpsOriginalAnalyticCuspLocalizedTaylor.comp (lpsOriginalAnalyticPrimeCoefficientEval p) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalCyclotomicPrimeCoefficientEval,lpsOriginalAnalyticPrimeCoefficientEval]
  · simp only [RingHom.comp_apply,lpsOriginalCyclotomicPrimeCoefficientEval,
      lpsOriginalAnalyticPrimeCoefficientEval,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    change lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p)
      (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) p
        (Fact.out : p.Prime).ne_zero)=
      lpsOriginalAnalyticCuspLocalizedTaylor
        (lpsOriginalAnalyticCuspAffineBranch p (Fact.out : p.Prime).pos 0)
    rw [lpsOriginalCuspCoefficientMap_jWidth,lpsOriginalAnalyticCuspAffineBranch_taylor_zero_phase]
end QEC.Coding.TannerLiftedProduct
