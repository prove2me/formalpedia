-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:38.561755+00:00
-- url     : https://prove2.me/submissions/8886780d-fb75-4385-9430-4d521bdc1340

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_neg_one_zpow_eq_jacobiParitySign
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiHalfTriangularDegree_nat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution (t : ℕ) :
    signedEuler (jtpIntegerTerm ((t : ℤ) + 1)) +
        signedEuler (jtpIntegerTerm (-(t : ℤ))) =
      -signedTriangularTerm (t : ℤ) := by
  cases t with
  | zero =>
      rw [jtpIntegerTerm, if_pos (by omega),
        jtpIntegerTerm, if_pos (by omega)]
      norm_num
      rw [jtpPositiveTerm, jtpPositiveTerm,
        signedEuler_C_T_mul_X_pow, signedEuler_C_T_mul_X_pow,
        signedTriangularTerm]
      norm_num [jacobiParitySign, jacobiHalfTriangularDegree]
  | succ t =>
      rw [jtpIntegerTerm, if_pos (by omega),
        jtpIntegerTerm, if_neg (by omega)]
      norm_num
      rw [show ((t : ℤ) + 1 + 1).toNat = t + 2 by omega]
      rw [jtpPositiveTerm, jtpNegativeTerm,
        signedEuler_C_T_mul_X_pow, signedEuler_C_T_mul_X_pow,
        signedTriangularTerm]
      rw [show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by omega,
        jacobiHalfTriangularDegree_nat]
      rw [← neg_one_zpow_eq_jacobiParitySign]
      push_cast
      rw [show ((-1 : ℚ) ^ ((t : ℤ) + 2)) = ((-1 : ℚ) ^ (t : ℤ)) by
        rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
        norm_num]
      rw [show ((-1 : ℚ) ^ (-(t : ℤ) - 1)) =
          -((-1 : ℚ) ^ (t : ℤ)) by
        rw [show -(t : ℤ) - 1 = -(t : ℤ) + (-1 : ℤ) by ring,
          zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0), zpow_neg]
        norm_num
        rcases neg_one_pow_eq_or ℚ t with h | h <;> simp [h]]
      rw [show ((-1 : ℚ) ^ ((t : ℤ) + 1)) =
          -((-1 : ℚ) ^ (t : ℤ)) by
        rw [zpow_add₀ (by norm_num : (-1 : ℚ) ≠ 0)]
        norm_num]
      rw [show t + 1 + 1 = t + 2 by omega]
      ext n
      simp only [map_add, map_neg, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow]
      split_ifs <;> ring
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
