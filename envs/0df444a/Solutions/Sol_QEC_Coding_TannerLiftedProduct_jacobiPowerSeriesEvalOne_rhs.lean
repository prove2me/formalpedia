-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_rhs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:54:42.728702+00:00
-- url     : https://prove2.me/submissions/74d2ac46-83e1-46ba-acec-2f76bdc70fab

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLaurentEvalOne_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_C_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_rhs_terms
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
    jacobiPowerSeriesEvalOne JacobiTripleProductCore.rhs =
      rationalIntegerThetaSeries := by
  letI : TopologicalSpace (LaurentPolynomial ℤ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℤ) := ⟨rfl⟩
  letI := JacobiTripleProductCore.piTop
  ext n
  simp only [jacobiPowerSeriesEvalOne, PowerSeries.coeff_map,
    coeff_rationalIntegerThetaSeries]
  have hCoeff : Summable (fun m : ℤ =>
      PowerSeries.coeff n
        (PowerSeries.C (LaurentPolynomial.T m) *
          JacobiTripleProductCore.q ^ m.natAbs ^ 2)) :=
    JacobiTripleProductCore.summable_rhs_terms.map
      (PowerSeries.coeff n)
      (PowerSeries.WithPiTopology.continuous_coeff
        (LaurentPolynomial ℤ) n)
  rw [JacobiTripleProductCore.rhs,
    JacobiTripleProductCore.summable_rhs_terms.map_tsum
      (PowerSeries.coeff n)
      (PowerSeries.WithPiTopology.continuous_coeff
        (LaurentPolynomial ℤ) n),
    hCoeff.map_tsum jacobiLaurentEvalOne continuous_of_discreteTopology]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    mul_ite, mul_one, mul_zero]
  rw [tsum_eq_sum (s := integerSquareRoots n) (fun m hm => by
    rw [if_neg]
    · simp
    · intro hsq
      apply hm
      rw [mem_integerSquareRoots_iff]
      rw [← sq_abs m, ← Int.natCast_natAbs m, ← Nat.cast_pow]
      exact_mod_cast hsq.symm)]
  calc
    _ = ∑ _m ∈ integerSquareRoots n, (1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [if_pos]
      · exact jacobiLaurentEvalOne_T m
      · rw [mem_integerSquareRoots_iff] at hm
        rw [← Nat.cast_inj (R := ℤ), Nat.cast_pow,
          Int.natCast_natAbs, sq_abs, hm]
    _ = _ := by simp
end QEC.Coding.TannerLiftedProduct
