-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrickeOrderMap_generatedDiagram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:19:10.02944+00:00
-- url     : https://prove2.me/submissions/da837218-0017-4bb6-931b-caa5d85421bb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
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
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGaussAffineToGenerated N hN p).comp
      (lpsOriginalGaussFrickeOrderMap N hN p hpN) =
        (lpsOriginalRationalFrickePullback N hN).comp
          (lpsOriginalGaussAffineToGenerated N hN p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  apply AdjoinRoot.ringHom_ext
  · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · apply Subtype.ext
      change (lpsOriginalGaussAffineToGenerated N hN p
        (lpsOriginalGaussFrickeOrderMap N hN p hpN
          (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
            (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)))).val =
        (lpsOriginalRationalFrickePullback N hN
          (lpsOriginalGaussAffineToGenerated N hN p
            (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
              (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)))).val
      rw [lpsOriginalGaussFrickeOrderMap_j, lpsOriginalGaussAffineToGenerated_root,
        lpsOriginalRationalFrickePullback_coe, lpsOriginalGaussAffineToGenerated_j,
        lpsOriginalPositiveFractionPullback_fricke_j]
  · apply Subtype.ext
    change (lpsOriginalGaussAffineToGenerated N hN p
      (lpsOriginalGaussFrickeOrderMap N hN p hpN
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))).val =
      (lpsOriginalRationalFrickePullback N hN
        (lpsOriginalGaussAffineToGenerated N hN p
          (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))).val
    rw [lpsOriginalGaussFrickeOrderMap_root, lpsOriginalGaussAffineToGenerated_j,
      lpsOriginalRationalFrickePullback_coe, lpsOriginalGaussAffineToGenerated_root,
      lpsOriginalPositiveFractionPullback_fricke_jN]
end QEC.Coding.TannerLiftedProduct
