-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioCosetPolynomial_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:38:34.58383+00:00
-- url     : https://prove2.me/submissions/2d3d7846-6763-4910-bff3-70e6ad7ae1d3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
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
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ).natDegree ≤
      Nat.card (LPSOriginalMeromorphicCosets N) := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  unfold lpsOriginalMeromorphicRatioCosetPolynomial
  refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
  calc
    _ ≤ ∑ _q : LPSOriginalMeromorphicCosets N, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)
    _ = _ := by simp [Nat.card_eq_fintype_card]
end QEC.Coding.TannerLiftedProduct
