-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_prime_eq_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:39:03.403574+00:00
-- url     : https://prove2.me/submissions/c20f3ac1-19c8-4fbd-bc03-ee7393c39516

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteField_square_sum_eq_gauss
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
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
    lpsUnaryQuadraticGauss a q=lpsQuadraticE2Character q (a:ZMod q)*
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) := by
  let ψ := (ZMod.stdAddChar (N:=q)).mulShift (a:ZMod q)
  have hψn : ψ≠1 := ZMod.isPrimitive_stdAddChar q ha
  have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψn
  have hF : ringChar (ZMod q)≠2 := by rw [ZMod.ringChar_zmod_n];exact hq2
  have h := lpsFiniteField_square_sum_eq_gauss (ZMod q) hF ψ hψ
  have hg : lpsUnaryQuadraticGauss a q=(∑ x : ZMod q,ψ (x^2)) := by
    rw [←lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier]
    simp only [zero_mul,add_zero,ψ,AddChar.mulShift_apply]
  rw [hg,h]
  change gaussSum (lpsQuadraticE2Character q) ((ZMod.stdAddChar (N:=q)).mulShift (a:ZMod q))=_
  have hu : IsUnit (a:ZMod q) := isUnit_iff_ne_zero.mpr ha
  have hs := gaussSum_mulShift_eq (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)) hu.unit
  have hchi : (lpsQuadraticE2Character q).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)
  rw [hchi.inv] at hs
  simpa only [hu.unit_spec] using hs
end QEC.Coding.TannerLiftedProduct
