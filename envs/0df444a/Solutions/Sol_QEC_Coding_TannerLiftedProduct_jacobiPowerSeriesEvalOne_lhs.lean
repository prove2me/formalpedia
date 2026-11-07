-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_lhs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:42:56.99899+00:00
-- url     : https://prove2.me/submissions/18d3167d-3d12-4d9c-8f92-743429a22edc

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLaurentEvalOne_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_C_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_qPochhammerInf
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factors_multipliable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_multipliable_P3_factors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_multipliable_factors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tprod_jacobi_theta_factor
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
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


attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiLaurentEvalOne_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_X
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_C_T

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiPowerSeriesEvalOne JacobiTripleProductCore.lhs =
      jacobiThetaProduct := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  have hSecond : Multipliable (fun n : ℕ =>
      1 - (-JacobiTripleProductCore.q * JacobiTripleProductCore.a) *
        (JacobiTripleProductCore.q ^ 2) ^ n) := by
    exact (JacobiTripleProductCore.factors_multipliable
      JacobiTripleProductCore.a).congr fun n => by ring
  rw [JacobiTripleProductCore.lhs]
  simp only [map_mul]
  rw [jacobiPowerSeriesEvalOne_qPochhammerInf _
      JacobiTripleProductCore.multipliable_factors,
    jacobiPowerSeriesEvalOne_qPochhammerInf _ hSecond,
    jacobiPowerSeriesEvalOne_qPochhammerInf _
      JacobiTripleProductCore.multipliable_P3_factors]
  simp only [map_pow, map_neg, map_mul,
    jacobiPowerSeriesEvalOne_X, jacobiPowerSeriesEvalOne_C_T]
  simp_rw [show ∀ n : ℕ,
      (1 : ℚ⟦X⟧) - PowerSeries.X ^ 2 * PowerSeries.X ^ (2 * n) =
        1 - PowerSeries.X ^ (2 * (n + 1)) by
          intro n
          rw [← pow_add]
          congr 2
          omega]
  simp_rw [show ∀ n : ℕ,
      (1 : ℚ⟦X⟧) - (-PowerSeries.X * 1) * PowerSeries.X ^ (2 * n) =
        1 + PowerSeries.X ^ (2 * n + 1) by
          intro n
          rw [show 2 * n + 1 = 1 + 2 * n by omega, pow_add]
          ring]
  rw [jacobiThetaProduct, tprod_jacobi_theta_factor]
  ring
end QEC.Coding.TannerLiftedProduct
