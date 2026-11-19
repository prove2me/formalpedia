-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_untwisted_cusp_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:42:51.020943+00:00
-- url     : https://prove2.me/submissions/b4436991-d4f0-45d6-801b-f7b1d8fb78cf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinTwoWeight_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_two_prime_product
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    (∑ a : Fin 5,∑ b : Fin 3,
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)*
        (1-(Int.gcd ((2^a.val*q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val*q^b.val:ℕ):ℂ)))=
      -lpsThetaEisensteinTwoCuspFactor γ*lpsThetaEisensteinPrimeCuspFactor q γ := by
  have he (a : Fin 5) (b : Fin 3) :
      (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)*
        (1-(Int.gcd ((2^a.val*q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val*q^b.val:ℕ):ℂ))=
      lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b-
        (lpsThetaEisensteinTwoWeight a*(Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ))*
          (lpsThetaEisensteinPrimeWeight q b*(Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)) := by
    rw [lpsEisensteinCuspGcd_two_prime_product q hq2]
    simp only [Nat.cast_mul]
    ring
  simp_rw [he,Finset.sum_sub_distrib]
  simp only [←Finset.mul_sum,←Finset.sum_mul,lpsThetaEisensteinTwoWeight_sum,
    zero_mul,zero_sub,lpsThetaEisensteinTwoCuspFactor,lpsThetaEisensteinPrimeCuspFactor,neg_mul]
end QEC.Coding.TannerLiftedProduct
