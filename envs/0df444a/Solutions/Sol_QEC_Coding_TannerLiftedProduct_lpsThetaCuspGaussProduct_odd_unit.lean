-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_odd_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:39:30.570199+00:00
-- url     : https://prove2.me/submissions/178638ef-83ca-452d-91b8-bff201b58887

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_unit_square
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_fourth_classified
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
theorem _root_.solution (q N : ℕ) [NeZero N] (hN : Odd N)
    (a : ℤ) (ha : IsUnit (a:ZMod N)) (hq : IsUnit ((2*q:ℕ):ZMod N)) :
    lpsThetaCuspGaussProduct q a N=(N:ℂ)^2 := by
  have he : 4*(q:ℤ)^2*a=a*((2*q:ℕ):ℤ)^2 := by push_cast;ring
  rw [lpsThetaCuspGaussProduct,he,lpsUnaryQuadraticGauss_unit_square N a ((2*q:ℕ):ℤ) (by exact_mod_cast hq)]
  rw [show lpsUnaryQuadraticGauss a N*lpsUnaryQuadraticGauss a N^3=lpsUnaryQuadraticGauss a N^4 by ring,
    lpsUnaryQuadraticGauss_fourth_classified N a ha]
  simp [lpsGaussFourthFactor,Nat.odd_iff.mp hN]
end QEC.Coding.TannerLiftedProduct
