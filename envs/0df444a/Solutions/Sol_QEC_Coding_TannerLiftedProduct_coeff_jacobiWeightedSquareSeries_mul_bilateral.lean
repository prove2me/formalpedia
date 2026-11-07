-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries_mul_bilateral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:25.611254+00:00
-- url     : https://prove2.me/submissions/399ce3b4-e434-4029-8900-0b47f4ccd9a9

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
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


attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n
        (jacobiWeightedSquareSeries * rationalBilateralTriangularSeries) =
      ∑ p : JacobiReindexedPair n, (2 * (p.1.2 : ℚ)) ^ 2 := by
  rw [PowerSeries.coeff_mul, ← Finset.sum_attach]
  simp only [Finset.attach_eq_univ, coeff_jacobiWeightedSquareSeries,
    coeff_rationalBilateralTriangularSeries]
  calc
    (∑ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
        (∑ t ∈ integerSquareRoots ij.1.1, (2 * (t : ℚ)) ^ 2) *
          ((integerTriangularRoots ij.1.2).card : ℚ)) =
      ∑ w : JacobiReindexedCoeffWitness n,
        (2 * (w.2.1.1 : ℚ)) ^ 2 := by
          rw [Fintype.sum_sigma]
          apply Fintype.sum_congr
          intro ij
          rw [Fintype.sum_prod_type]
          simp
          rw [← Finset.mul_sum]
          have hsum :
              (∑ t ∈ (integerSquareRoots ij.1.1).attach,
                (2 * (t.1 : ℚ)) ^ 2) =
                ∑ t ∈ integerSquareRoots ij.1.1,
                  (2 * (t : ℚ)) ^ 2 :=
            Finset.sum_attach (integerSquareRoots ij.1.1)
              (fun t : ℤ => (2 * (t : ℚ)) ^ 2)
          rw [hsum]
          ring
    _ = ∑ w : JacobiReindexedCoeffWitness n,
        (2 * ((jacobiReindexedCoeffWitnessEquiv n w).1.2 : ℚ)) ^ 2 := by
      rfl
    _ = ∑ p : JacobiReindexedPair n, (2 * (p.1.2 : ℚ)) ^ 2 :=
      Equiv.sum_comp (jacobiReindexedCoeffWitnessEquiv n)
        (fun p : JacobiReindexedPair n => (2 * (p.1.2 : ℚ)) ^ 2)
end QEC.Coding.TannerLiftedProduct
