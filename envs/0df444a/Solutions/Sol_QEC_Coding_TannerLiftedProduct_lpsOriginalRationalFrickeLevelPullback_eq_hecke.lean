-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalFrickeLevelPullback_eq_hecke
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:58:15.773626+00:00
-- url     : https://prove2.me/submissions/0912c685-8a01-4ece-bbbe-1a0f38fceedb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
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
open scoped UpperHalfPlane MatrixGroups
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
      (Nat.mul_pos hN hp) = lpsOriginalRationalHeckePullback N p hN hp h4N := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let fN := lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
    (lpsOriginalFrickeMatrix_pos N hN)
  let fM := lpsOriginalPositiveFractionPullback
    (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
    (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))
  have hg : Set.EqOn (fM.toRingHom.comp fN.toRingHom)
      (lpsOriginalDilationFractionPullback p hp).toRingHom
      {lpsOriginalJInFractionField,lpsOriginalJNInFractionField N hN} := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hy | hy
    · subst y
      change fM (fN lpsOriginalJInFractionField) =
        lpsOriginalDilationFractionPullback p hp lpsOriginalJInFractionField
      simp only [fN,fM,lpsOriginalPositiveFractionPullback_fricke_j,
        lpsOriginalDilationFractionPullback_j]
      exact lpsOriginalPositiveFractionPullback_fricke_product_jN N p hN hp
    · have he := Set.mem_singleton_iff.mp hy
      subst y
      change fM (fN (lpsOriginalJNInFractionField N hN)) =
        lpsOriginalDilationFractionPullback p hp (lpsOriginalJNInFractionField N hN)
      simp only [fN,fM,lpsOriginalPositiveFractionPullback_fricke_jN,
        lpsOriginalPositiveFractionPullback_fricke_j,lpsOriginalDilationFractionPullback_jN]
  apply RingHom.ext
  intro x
  apply Subtype.ext
  change fM (fN (x : LPSOriginalHolomorphicFractionField)) =
    lpsOriginalDilationFractionPullback p hp x
  apply RingHom.eqOn_field_closure hg
  rw [← lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure N hN]
  exact x.property
end QEC.Coding.TannerLiftedProduct
