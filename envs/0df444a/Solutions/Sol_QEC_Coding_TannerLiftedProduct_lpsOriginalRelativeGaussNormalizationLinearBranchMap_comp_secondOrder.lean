-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationLinearBranchMap_comp_secondOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:19:59.06288+00:00
-- url     : https://prove2.me/submissions/a97e3948-ae72-4832-8ceb-60bbaf42dbef

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_base
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__frobenius_e48cc4f8f4fd
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_eval__hom_5c9005d9bf86
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_integerBaseEval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchMap_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondJ
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
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    (lpsOriginalRelativeGaussNormalizationLinearBranchMap N p hNp h4N hN hpN q).comp
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) =
      (frobenius (LPSOriginalGaussAffineOrder N hN p ⧸ q) p).comp (Ideal.Quotient.mk q) := by
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply,lpsOriginalRelativeGaussNormalizationSecondOrderMap_base]
    rw [lpsOriginalRelativeGaussNormalizationSecondBaseMap_integer]
    have hP := RingHom.congr_fun (lpsOriginalGaussMaximalResidue_integerBaseEval N hN p q) P
    change Ideal.Quotient.mk q
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P)) = _ at hP
    rw [hP]
    change _ = (P.eval₂ (Int.castRingHom K) (lpsOriginalGaussMaximalResidueJ N hN p q))^p
    rw [lpsOriginalIntegerPolynomial_eval₂_hom,
      lpsOriginalRelativeGaussNormalizationLinearBranchMap_secondJ,
      ← lpsOriginalIntegerPolynomial_eval₂_frobenius]
  · simp only [RingHom.comp_apply,lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
      lpsOriginalRelativeGaussNormalizationLinearBranchMap_root,frobenius_def]
    rfl
end QEC.Coding.TannerLiftedProduct
