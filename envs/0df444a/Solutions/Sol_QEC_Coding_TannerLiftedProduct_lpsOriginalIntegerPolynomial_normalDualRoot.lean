-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_normalDualRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:03:35.353403+00:00
-- url     : https://prove2.me/submissions/50ca7cf4-fdd5-46b2-8ee3-71a64a07a342

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJ_generated
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
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (lpsOriginalIntegerFrickeCoefficientMap N hN)
      (lpsOriginalIntegerNormalJ N hN) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let f := (integralClosure (Polynomial ℤ)
    (lpsOriginalGeneratedFunctionFieldQ N hN)).val.toRingHom
  have hc : f.comp (lpsOriginalIntegerFrickeCoefficientMap N hN) =
      Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJNElement N hN) := by
    apply Polynomial.ringHom_ext
    · intro z
      have hz : Polynomial.C z = (z : Polynomial ℤ) := by simp
      rw [hz,map_intCast,map_intCast]
    · simp only [RingHom.comp_apply,lpsOriginalIntegerFrickeCoefficientMap,
        Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
      rfl
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext h
  apply hf
  rw [Polynomial.hom_eval₂,map_zero,hc]
  change (lpsOriginalIntegerPolynomial N hN).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom _) (lpsOriginalRationalJNElement N hN))
    (lpsOriginalIntegerNormalJ N hN).val = 0
  rw [lpsOriginalIntegerNormalJ_generated]
  exact lpsOriginalIntegerPolynomial_frickeSwappedRoot N hN
end QEC.Coding.TannerLiftedProduct
