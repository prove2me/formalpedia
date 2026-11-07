-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:08.225326+00:00
-- url     : https://prove2.me/submissions/230c353a-ec0b-469a-87e0-ad119c893869

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParitySign_add
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
section
namespace QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
private theorem jacobiCubeCoeffWitnessWeight_eq_pairWeight
    {n : ℕ} (w : JacobiCubeCoeffWitness n) :
    jacobiCubeCoeffWitnessWeight w =
      jacobiCubePairWeight (jacobiCubeCoeffWitnessEquiv n w).1 := by
  rw [jacobiCubeCoeffWitnessWeight, jacobiCubePairWeight]
  change
    (jacobiParitySign w.2.1.1 * (2 * (w.2.1.1 : ℚ) + 1)) *
        (jacobiParitySign w.2.2.1 * (2 * (w.2.2.1 : ℚ) + 1)) =
      jacobiParitySign (w.2.1.1 + w.2.2.1) *
        (2 * (w.2.1.1 : ℚ) + 1) * (2 * (w.2.2.1 : ℚ) + 1)
  rw [← jacobiParitySign_add]
  ring
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n (jacobiSignedCubeSeriesRaw ^ 2) =
      ∑ p : JacobiCubePair n, jacobiCubePairWeight p.1 := by
  rw [pow_two, PowerSeries.coeff_mul, ← Finset.sum_attach]
  simp only [Finset.attach_eq_univ, coeff_jacobiSignedCubeSeriesRaw]
  calc
    (∑ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
        (∑ k : {k : ℤ // k ∈ integerTriangularRoots (2 * ij.1.1)},
          jacobiParitySign k.1 * (2 * (k.1 : ℚ) + 1)) *
        ∑ l : {l : ℤ // l ∈ integerTriangularRoots (2 * ij.1.2)},
          jacobiParitySign l.1 * (2 * (l.1 : ℚ) + 1)) =
      ∑ w : JacobiCubeCoeffWitness n,
        jacobiCubeCoeffWitnessWeight w := by
          rw [Fintype.sum_sigma]
          apply Fintype.sum_congr
          intro ij
          rw [Fintype.sum_prod_type]
          exact Fintype.sum_mul_sum _ _
    _ = ∑ w : JacobiCubeCoeffWitness n,
        jacobiCubePairWeight (jacobiCubeCoeffWitnessEquiv n w).1 := by
      apply Fintype.sum_congr
      exact jacobiCubeCoeffWitnessWeight_eq_pairWeight
    _ = ∑ p : JacobiCubePair n, jacobiCubePairWeight p.1 :=
      Equiv.sum_comp (jacobiCubeCoeffWitnessEquiv n)
        (fun p : JacobiCubePair n => jacobiCubePairWeight p.1)
end QEC.Coding.TannerLiftedProduct
