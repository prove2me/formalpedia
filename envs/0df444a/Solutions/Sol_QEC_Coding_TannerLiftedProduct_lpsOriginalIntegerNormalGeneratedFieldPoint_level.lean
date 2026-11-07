-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGeneratedFieldPoint_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:12:43.15999+00:00
-- url     : https://prove2.me/submissions/582b2029-ea92-4004-bf06-8a692e0b124a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_chart
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
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Spec.map (CommRingCat.ofHom
      (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN =
    lpsOriginalIntegerNormalGeneratedFieldPoint M hM ≫
      lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField M hM).toAlgebra
  have he : CommRingCat.ofHom (algebraMap
        (lpsOriginalIntegerNormalZeroChart N hN)
          (lpsOriginalGeneratedFunctionFieldQ N hN)) ≫
        CommRingCat.ofHom (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom =
      CommRingCat.ofHom (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM) ≫
        CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart M hM)
          (lpsOriginalGeneratedFunctionFieldQ M hM)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply Subtype.ext
    rfl
  dsimp only [lpsOriginalIntegerNormalGeneratedFieldPoint]
  rw [Category.assoc, lpsOriginalIntegerNormalGluedForgetLevel_chart]
  change Spec.map (CommRingCat.ofHom
      (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart N hN)
        (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN false) =
    Spec.map (CommRingCat.ofHom (algebraMap (lpsOriginalIntegerNormalZeroChart M hM)
      (lpsOriginalGeneratedFunctionFieldQ M hM))) ≫
      (Spec.map (CommRingCat.ofHom
        (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM)) ≫
          lpsOriginalIntegerNormalGluedChartMap N hN false)
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, he]
end QEC.Coding.TannerLiftedProduct
