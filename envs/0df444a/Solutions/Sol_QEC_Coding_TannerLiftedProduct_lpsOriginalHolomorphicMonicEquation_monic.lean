-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicMonicEquation_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:55:09.305868+00:00
-- url     : https://prove2.me/submissions/a719d101-06b4-488b-a6b8-2b93f0493973

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDenominatorEquation_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_degree
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
theorem _root_.solution (N : ℕ) [NeZero N] (k : ℕ)
    (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalHolomorphicMonicEquation N k A).Monic := by
  let r := Nat.card (LPSOriginalMeromorphicCosets N)
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one r
  · unfold lpsOriginalHolomorphicMonicEquation
    apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C,zero_add,r] using
      (lpsOriginalMeromorphicRatioEquation_degree N k A (lpsOriginalMeromorphicDeltaPowerAtLevel N k))
  · rw [lpsOriginalHolomorphicMonicEquation,Polynomial.coeff_C_mul,
      lpsOriginalDeltaDenominatorEquation_coeff,← Polynomial.C_mul,inv_mul_cancel₀]
    · exact Polynomial.C_1
    · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
end QEC.Coding.TannerLiftedProduct
