-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:33:18.03819+00:00
-- url     : https://prove2.me/submissions/db479aed-5dcd-4634-8081-97e64582c2bc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_j
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalFrickeLevelPullback_eq_hecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationRoot_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondJ_coe
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
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ a : LPSOriginalGaussAffineOrder N hN p,
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN a).val =
        lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)
          (lpsOriginalGaussAffineToGenerated N hN p a) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let : (lpsOriginalGaussPrime p).IsPrime := lpsOriginalGaussPrime_isPrime p
  let v : LPSOriginalRelativeGaussNormalization N p hNp h4N hN →+* L :=
    (integralClosure A L).val.toRingHom
  let f := v.comp (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN)
  let g := (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N).comp
    (lpsOriginalGaussAffineToGenerated N hN p)
  have h : f = g := by
    apply AdjoinRoot.ringHom_ext
    · apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
      apply Polynomial.ringHom_ext
      · intro z
        simp
      · apply Subtype.ext
        change (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
          (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
            (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))).val.val =
          (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N
            (lpsOriginalGaussAffineToGenerated N hN p
              (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
                (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)))).val
        rw [lpsOriginalRelativeGaussNormalizationSecondOrderMap_j,
          lpsOriginalRelativeGaussNormalizationSecondJ_coe,
          lpsOriginalRationalHeckePullback_coe,lpsOriginalGaussAffineToGenerated_j,
          lpsOriginalDilationFractionPullback_j]
    · apply Subtype.ext
      change (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val.val =
        (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N
          (lpsOriginalGaussAffineToGenerated N hN p
            (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)))).val
      rw [lpsOriginalRelativeGaussNormalizationSecondOrderMap_root,
        lpsOriginalRelativeGaussNormalizationRoot_coe,
        lpsOriginalRationalHeckePullback_coe,lpsOriginalGaussAffineToGenerated_root,
        lpsOriginalDilationFractionPullback_jN]
  intro a
  rw [lpsOriginalRationalFrickeLevelPullback_eq_hecke]
  exact RingHom.congr_fun h a
end QEC.Coding.TannerLiftedProduct
