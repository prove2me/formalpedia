-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.substNegX_X_mul_jacobiPlusLogDerivative_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:55:05.910541+00:00
-- url     : https://prove2.me/submissions/08eb5144-82f9-4388-8a52-b91ca8bea479

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLambertTerm_eq_X_pow_mul_geometric
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertTerm
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiGeometricSeries_subst_mul_one_sub_X_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLaurentEvalOne_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_C_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiLaurentEvalOne_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_C_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_X
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


section
namespace QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
private theorem neg_X_pow_even (n : ℕ) :
    (-(PowerSeries.X : PowerSeries ℚ)) ^ (2 * n) =
      PowerSeries.X ^ (2 * n) := by
  rw [neg_pow, (even_two_mul n).neg_one_pow]
  ring
private theorem neg_X_pow_odd (n : ℕ) :
    (-(PowerSeries.X : PowerSeries ℚ)) ^ (2 * n + 1) =
      -(PowerSeries.X ^ (2 * n + 1)) := by
  rw [pow_add, neg_X_pow_even]
  ring
private theorem isUnit_one_sub_X_pow {d : ℕ} (hd : d ≠ 0) :
    IsUnit ((1 : PowerSeries ℚ) - PowerSeries.X ^ d) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [hd]
private theorem isUnit_one_add_X_pow {d : ℕ} (hd : d ≠ 0) :
    IsUnit ((1 : PowerSeries ℚ) + PowerSeries.X ^ d) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp [hd]
private theorem substNegX_geometric_neg_even (n : ℕ) :
    substNegX
        (jacobiGeometricSeries.subst
          (-(PowerSeries.X ^ (2 * (n + 1))))) =
      jacobiGeometricSeries.subst
        (-(PowerSeries.X ^ (2 * (n + 1)))) := by
  have hd : 2 * (n + 1) ≠ 0 := by omega
  apply (isUnit_one_add_X_pow hd).mul_right_cancel
  have hmap :
      substNegX
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * (n + 1))) =
        1 + PowerSeries.X ^ (2 * (n + 1)) := by
    simp only [map_add, map_one, map_pow, substNegX_X]
    rw [neg_X_pow_even]
  calc
    substNegX
          (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * (n + 1))))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) =
      substNegX
          (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * (n + 1))))) *
        substNegX
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * (n + 1))) := by
            rw [hmap]
    _ = substNegX
        (jacobiGeometricSeries.subst
            (-(PowerSeries.X ^ (2 * (n + 1)))) *
          ((1 : PowerSeries ℚ) + PowerSeries.X ^ (2 * (n + 1)))) := by
            rw [map_mul]
    _ = substNegX 1 := congrArg substNegX
      (jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow hd)
    _ = 1 := map_one substNegX
    _ = jacobiGeometricSeries.subst
          (-(PowerSeries.X ^ (2 * (n + 1)))) *
        (1 + PowerSeries.X ^ (2 * (n + 1))) :=
      (jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow hd).symm
private theorem geometric_double_mul_one_add (d : ℕ) (hd : d ≠ 0) :
    jacobiGeometricSeries.subst
          ((PowerSeries.X : PowerSeries ℚ) ^ (2 * d)) *
        (1 + (PowerSeries.X : PowerSeries ℚ) ^ d) =
      jacobiGeometricSeries.subst
        ((PowerSeries.X : PowerSeries ℚ) ^ d) := by
  apply (isUnit_one_sub_X_pow hd).mul_right_cancel
  calc
    (jacobiGeometricSeries.subst (PowerSeries.X ^ (2 * d)) *
          (1 + PowerSeries.X ^ d)) *
        (1 - PowerSeries.X ^ d) =
      jacobiGeometricSeries.subst (PowerSeries.X ^ (2 * d)) *
        (1 - PowerSeries.X ^ (2 * d)) := by
          rw [show 2 * d = d * 2 by omega, pow_mul]
          ring
    _ = 1 := jacobiGeometricSeries_subst_mul_one_sub_X_pow
      (show 2 * d ≠ 0 by omega)
    _ = jacobiGeometricSeries.subst (PowerSeries.X ^ d) *
        (1 - PowerSeries.X ^ d) :=
      (jacobiGeometricSeries_subst_mul_one_sub_X_pow hd).symm
private theorem plusFraction_eq_lambert_sub_double (d : ℕ) (hd : d ≠ 0) :
    PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
        jacobiGeometricSeries.subst (-(PowerSeries.X ^ d)) =
      jacobiLambertTerm d - jacobiLambertTerm (2 * d) := by
  rw [jacobiLambertTerm_eq_X_pow_mul_geometric hd,
    jacobiLambertTerm_eq_X_pow_mul_geometric
      (show 2 * d ≠ 0 by omega)]
  apply (isUnit_one_add_X_pow hd).mul_right_cancel
  have hneg := jacobiGeometricSeries_subst_neg_X_pow_mul_one_add_X_pow hd
  have hpos := jacobiGeometricSeries_subst_mul_one_sub_X_pow hd
  have hdouble := geometric_double_mul_one_add d hd
  calc
    (PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
          jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))) *
        (1 + PowerSeries.X ^ d) =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ d := by
        rw [mul_assoc, hneg]
        ring
    _ = PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
          jacobiGeometricSeries.subst (PowerSeries.X ^ d) *
          (1 + PowerSeries.X ^ d) -
        PowerSeries.C ((2 * d : ℕ) : ℚ) * PowerSeries.X ^ (2 * d) *
          (jacobiGeometricSeries.subst (PowerSeries.X ^ (2 * d)) *
            (1 + PowerSeries.X ^ d)) := by
      rw [hdouble]
      have hC : PowerSeries.C (((2 * d : ℕ) : ℚ)) =
          2 * PowerSeries.C (d : ℚ) := by
        push_cast
        rw [map_mul]
        change (2 : PowerSeries ℚ) * PowerSeries.C (d : ℚ) = _
        rfl
      have hpow :
          (PowerSeries.X : PowerSeries ℚ) ^ (d * 2) =
            (PowerSeries.X ^ d : PowerSeries ℚ) ^ 2 :=
        pow_mul _ _ _
      rw [hC, show 2 * d = d * 2 by omega]
      calc
        PowerSeries.C (d : ℚ) * PowerSeries.X ^ d =
            PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
              (jacobiGeometricSeries.subst (PowerSeries.X ^ d) *
                (1 - PowerSeries.X ^ d)) := by rw [hpos]; ring
        _ = _ := by rw [hpow]; ring
    _ = (PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
          jacobiGeometricSeries.subst (PowerSeries.X ^ d) -
        PowerSeries.C ((2 * d : ℕ) : ℚ) * PowerSeries.X ^ (2 * d) *
          jacobiGeometricSeries.subst (PowerSeries.X ^ (2 * d))) *
        (1 + PowerSeries.X ^ d) := by
      ring
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    substNegX
        (PowerSeries.X * jacobiPlusLogDerivative (2 * (n + 1))) =
      jacobiLambertTerm (2 * (n + 1)) -
        jacobiLambertTerm (4 * (n + 1)) := by
  let d := 2 * (n + 1)
  have hd : d ≠ 0 := by simp [d]
  rw [jacobiPlusLogDerivative]
  simp only [map_mul, map_pow, substNegX_X, substNegX_C]
  rw [show d - 1 = 2 * n + 1 by simp [d]; omega,
    neg_X_pow_odd n, substNegX_geometric_neg_even]
  have h := plusFraction_eq_lambert_sub_double d hd
  rw [show 2 * d = 4 * (n + 1) by simp [d]; ring] at h
  rw [show d = 2 * (n + 1) by rfl] at h
  convert h using 1
  all_goals ring
end QEC.Coding.TannerLiftedProduct
