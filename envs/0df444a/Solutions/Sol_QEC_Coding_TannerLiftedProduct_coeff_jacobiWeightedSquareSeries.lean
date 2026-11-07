-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:07:15.755503+00:00
-- url     : https://prove2.me/submissions/aab95015-2b3d-4048-92cd-435eede580a2

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n jacobiWeightedSquareSeries =
      ∑ z ∈ integerSquareRoots n, (2 * (z : ℚ)) ^ 2 := by
  simp [jacobiWeightedSquareSeries]
end QEC.Coding.TannerLiftedProduct
