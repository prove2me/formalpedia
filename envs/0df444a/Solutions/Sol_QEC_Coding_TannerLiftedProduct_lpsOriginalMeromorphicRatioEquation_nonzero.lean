-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:31.680418+00:00
-- url     : https://prove2.me/submissions/a5e8cdc7-4ab4-4d1a-a4d1-822ee6ff02e2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioCosetPolynomial_eval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_recovery
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (hB : B ≠ 0) :
    lpsOriginalMeromorphicRatioEquation N k A B ≠ 0 := by
  obtain ⟨c,hc⟩ : ∃ c : ℂ, A-c • B ≠ 0 := by
    by_cases hA : A = 0
    · refine ⟨1,?_⟩
      simpa [hA] using hB
    · refine ⟨0,?_⟩
      simpa using hA
  intro hzero
  have hnorm : lpsOriginalMeromorphicRatioNorm N k A B c ≠ 0 := by
    exact ModularForm.mcast_eq_zero_iff _ rfl _ |>.not.mpr
      (ModularForm.norm_ne_zero 𝒮ℒ (by
        intro hzero
        apply hc
        ext τ
        exact congr_fun hzero τ))
  apply hnorm
  ext τ
  have h := congrArg (fun P : Polynomial ℂ => P.eval c)
    (lpsOriginalMeromorphicRatioEquation_recovery N k A B τ)
  rw [hzero,Polynomial.map_zero,mul_zero,Polynomial.eval_zero,
    lpsOriginalMeromorphicRatioCosetPolynomial_eval] at h
  exact h.symm
end QEC.Coding.TannerLiftedProduct
