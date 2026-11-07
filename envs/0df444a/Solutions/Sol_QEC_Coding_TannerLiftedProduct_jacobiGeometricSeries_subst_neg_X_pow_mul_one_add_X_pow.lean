-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:51.954483+00:00
-- url     : https://prove2.me/submissions/a2e43762-f847-46a8-9795-b3f285e7b92a

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiGeometricSeries_subst_mul_one_sub
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


attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {d : ℕ} (hd : d ≠ 0) :
    (jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))) *
      ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) = 1 := by
  have hs : PowerSeries.HasSubst (-(PowerSeries.X ^ d) : ℚ⟦X⟧) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    have hx : MvPowerSeries.constantCoeff (PowerSeries.X : ℚ⟦X⟧) = 0 :=
      PowerSeries.constantCoeff_X
    rw [map_neg, map_pow, hx, zero_pow hd, neg_zero]
  simpa only [sub_neg_eq_add] using
    jacobiGeometricSeries_subst_mul_one_sub hs
end QEC.Coding.TannerLiftedProduct
