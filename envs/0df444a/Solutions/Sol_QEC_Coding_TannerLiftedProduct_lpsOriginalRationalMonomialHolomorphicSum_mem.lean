-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalMonomialHolomorphicSum_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:37:45.368843+00:00
-- url     : https://prove2.me/submissions/25831422-f439-4931-a6c8-65ebce52b24d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_C
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (u v : ι → ℕ) (a : ι → ℚ) :
    algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (lpsOriginalRationalMonomialHolomorphicSum M hM u v a) ∈
        lpsOriginalGeneratedFunctionFieldQ M hM := by
  classical
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let F := lpsOriginalGeneratedFunctionFieldQ M hM
  let holoMap := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hpoly (P : Polynomial ℚ) : holoMap (lpsOriginalJHolomorphicEvalQ P) ∈ F := by
    rw [← lpsOriginalJFractionEmbeddingQ_polynomial]
    exact F.algebraMap_mem _
  have hj : holoMap lpsOriginalJHolomorphic ∈ F := by
    rw [← lpsOriginalJHolomorphicEvalQ_X]
    exact hpoly Polynomial.X
  have hJM : holoMap (lpsOriginalJNHolomorphic M hM) ∈ F := by
    exact IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ)) _ (Set.mem_singleton _)
  change holoMap (∑ i, algebraMap ℚ LPSOriginalHolomorphicRing (a i) *
    lpsOriginalJHolomorphic ^ u i * lpsOriginalJNHolomorphic M hM ^ v i) ∈ F
  simp only [map_sum, map_mul, map_pow]
  apply F.sum_mem
  intro i _hi
  apply F.mul_mem
  · apply F.mul_mem
    · rw [← lpsOriginalJHolomorphicEvalQ_C]
      exact hpoly (Polynomial.C (a i))
    · exact pow_mem hj (u i)
  · exact pow_mem hJM (v i)
end QEC.Coding.TannerLiftedProduct
