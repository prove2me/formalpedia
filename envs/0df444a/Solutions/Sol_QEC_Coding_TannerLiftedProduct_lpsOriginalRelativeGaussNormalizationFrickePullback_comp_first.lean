-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFrickePullback_comp_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:43:02.523216+00:00
-- url     : https://prove2.me/submissions/f7e9eedc-978a-4d82-9f07-4e32ef040e4c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFrickePullback_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationCoefficients_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationRoot_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondJ_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
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
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN).comp
      (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) =
        (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).comp
          (lpsOriginalGaussFrickeOrderMap N hN p hpN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp only [RingHom.comp_apply]
      apply Subtype.ext
      apply Subtype.ext
      rw [lpsOriginalGaussFrickeOrderMap_j,
        lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
        lpsOriginalRelativeGaussNormalizationRoot_coe,
        lpsOriginalRelativeGaussNormalizationFrickePullback_coe,
        lpsOriginalRationalFrickePullback_coe,
        lpsOriginalRelativeGaussNormalizationCoefficients_coe,
        lpsOriginalGaussAffineToGenerated_j,
        lpsOriginalPositiveFractionPullback_fricke_j]
  · simp only [RingHom.comp_apply]
    apply Subtype.ext
    apply Subtype.ext
    rw [lpsOriginalGaussFrickeOrderMap_root,
      lpsOriginalRelativeGaussNormalizationSecondOrderMap_j,
      lpsOriginalRelativeGaussNormalizationSecondJ_coe,
      lpsOriginalRelativeGaussNormalizationFrickePullback_coe,
      lpsOriginalRationalFrickePullback_coe,
      lpsOriginalRelativeGaussNormalizationCoefficients_coe,
      lpsOriginalGaussAffineToGenerated_root,
      lpsOriginalPositiveFractionPullback_fricke_product_jN]
end QEC.Coding.TannerLiftedProduct
