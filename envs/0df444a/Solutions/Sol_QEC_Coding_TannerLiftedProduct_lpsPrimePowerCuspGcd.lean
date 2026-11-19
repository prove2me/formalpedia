-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPrimePowerCuspGcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:48:50.83623+00:00
-- url     : https://prove2.me/submissions/681fda23-5be2-4179-bc85-51f6c561f310

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatGcd_same_base_powers
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsStandardThetaModularForm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p a t L : ℕ) (hc : p.Coprime L) :
    Int.gcd ((p^a:ℕ):ℤ) ((p^t*L:ℕ):ℤ)=p^(min a t) := by
  simp only [Int.gcd_def,Int.natAbs_natCast]
  rw [(hc.pow_left t).gcd_mul (p^a),(hc.pow_left a).gcd_eq_one,mul_one,
    lpsNatGcd_same_base_powers]
end QEC.Coding.TannerLiftedProduct
