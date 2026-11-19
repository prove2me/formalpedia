-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:00.685236+00:00
-- url     : https://prove2.me/submissions/b9bf73a8-117f-4290-bb27-9600285085a4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_prime_eq_character
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_inflate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsStandardThetaModularForm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : ℤ) (ha : (a:ZMod q)≠0) :
    lpsThetaCuspGaussProduct q a q=(q:ℂ)^3*lpsQuadraticE2Character q (a:ZMod q)*
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by
  have hz : lpsUnaryQuadraticGauss (4*(q:ℤ)^2*a) q=(q:ℂ) := by
    have h := lpsUnaryQuadraticGauss_inflate q 1 (4*(q:ℤ)*a)
    have he : 4*(q:ℤ)*a*(q:ℤ)=4*(q:ℤ)^2*a := by ring
    simpa only [he,mul_one,lpsUnaryQuadraticGauss_one] using h
  rw [lpsThetaCuspGaussProduct,hz,lpsUnaryQuadraticGauss_prime_eq_character q hq2 a ha]
  ring
end QEC.Coding.TannerLiftedProduct
