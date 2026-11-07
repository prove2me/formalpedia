-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.sum_jacobiCubePairWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:22.641121+00:00
-- url     : https://prove2.me/submissions/e0e97701-c287-4cb6-9a44-b68d6b24b445

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    (∑ p : JacobiCubePair n, jacobiCubePairWeight p.1) =
      2 * ∑ p : JacobiReindexedPair n, jacobiReindexedPairWeight p.1 := by
  calc
    (∑ p : JacobiCubePair n, jacobiCubePairWeight p.1) =
        ∑ p : JacobiReindexedPair n ⊕ JacobiReindexedPair n,
          jacobiCubePairWeight (jacobiCubePairEquiv n p).1 :=
      (Equiv.sum_comp (jacobiCubePairEquiv n)
        (fun p : JacobiCubePair n => jacobiCubePairWeight p.1)).symm
    _ = (∑ p : JacobiReindexedPair n, jacobiReindexedPairWeight p.1) +
        ∑ p : JacobiReindexedPair n, jacobiReindexedPairWeight p.1 := by
      rw [Fintype.sum_sum_type]
      congr 1
      · apply Fintype.sum_congr
        intro p
        simpa using jacobiCubePairWeight_equiv_inl n p
      · apply Fintype.sum_congr
        intro p
        simpa using jacobiCubePairWeight_equiv_inr n p
    _ = 2 * ∑ p : JacobiReindexedPair n,
        jacobiReindexedPairWeight p.1 := by ring
end QEC.Coding.TannerLiftedProduct
