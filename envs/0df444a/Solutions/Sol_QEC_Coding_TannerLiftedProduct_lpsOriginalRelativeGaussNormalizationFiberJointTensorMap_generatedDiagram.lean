-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_generatedDiagram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:51:45.565176+00:00
-- url     : https://prove2.me/submissions/c291e9e7-bb92-45dd-b037-b4d047a525ba

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective
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
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : CharP F p := charP_of_injective_ringHom
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    letI : Module (ZMod p) K := Algebra.toModule
    letI : Module (ZMod p) F := Algebra.toModule
    (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q).toRingHom.comp
      (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q).toRingHom =
        (lpsOriginalFrobeniusFirstTensorGraphMap p K).toRingHom.prod
          (lpsOriginalFrobeniusSecondTensorGraphMap p K).toRingHom := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  let e := lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv N p hNp h4N hN hpN q
  apply Algebra.TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro a
    change e ((lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q a) *
      (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q 1)) =
        (a * 1^p, a^p * 1)
    have h := RingHom.congr_fun
      (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_first N p hNp h4N hN hpN q) a
    change e (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q a) =
      (a, a^p) at h
    simpa only [map_one, mul_one, one_pow] using h
  · apply RingHom.ext
    intro b
    change e ((lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q 1) *
      (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q b)) =
        (1 * b^p, 1^p * b)
    have h := RingHom.congr_fun
      (lpsOriginalRelativeGaussNormalizationFiberFrobeniusRingEquiv_comp_second N p hNp h4N hN hpN q) b
    change e (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q b) =
      (b^p, b) at h
    simpa only [map_one, one_mul, one_pow] using h
end QEC.Coding.TannerLiftedProduct
