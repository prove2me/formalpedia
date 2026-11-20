-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProductLevelCoefficientMap_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:09:09.861185+00:00
-- url     : https://prove2.me/submissions/5cdf02bd-f872-45bd-9e5a-552abe63fb04

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNIntegerFractionEval_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJN_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProductLevelCoefficientMap_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroLevelPullback_coe
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerNormalToHolomorphic (N*p) (Nat.mul_pos hN hp)).comp
      (lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN hp) =
      lpsOriginalJNIntegerFractionEval N hN := by
  apply Polynomial.ringHom_ext
  · intro z
    have hz : Polynomial.C z = (z : Polynomial ℤ) := by
      simp
    rw [hz, map_intCast, map_intCast]
  · rw [RingHom.comp_apply, lpsOriginalIntegerProductLevelCoefficientMap_X,
      lpsOriginalJNIntegerFractionEval_X]
    change (((lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)
        (lpsOriginalIntegerNormalJN N hN)).val.val)) =
      lpsOriginalJNInFractionField N hN
    exact (lpsOriginalIntegerNormalZeroLevelPullback_coe N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)
        (lpsOriginalIntegerNormalJN N hN)).trans
      (lpsOriginalIntegerNormalJN_coe N hN)
end QEC.Coding.TannerLiftedProduct
