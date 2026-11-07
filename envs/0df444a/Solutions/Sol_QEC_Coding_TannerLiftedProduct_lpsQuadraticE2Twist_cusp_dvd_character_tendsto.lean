-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_dvd_character_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:00:44.888205+00:00
-- url     : https://prove2.me/submissions/24bd13d1-d414-496a-8bf5-419581feb7c0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCusp_delta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspGcd_weighted_of_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_gcd_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (hD : (D:ZMod q)≠0) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-(γ 0 0:ZMod q)/(D:ZMod q)))) := by
  have ht := lpsQuadraticE2Twist_cusp_gcd_tendsto q γ
  have hs := (ZMod.finEquiv q).sum_comp (fun r : ZMod q =>
    lpsQuadraticE2Character q r*(if (γ 0 0:ZMod q)+r*(D:ZMod q)=0 then (q:ℂ)^2 else 1))
  rw [lpsQuadraticEisensteinCusp_delta q hq2 _ _ hD] at hs
  change (∑ r : Fin q,lpsQuadraticE2Character q (ZMod.finEquiv q r)*
    (if (γ 0 0:ZMod q)+(ZMod.finEquiv q r)*(D:ZMod q)=0 then (q:ℂ)^2 else 1))=_ at hs
  simp only [←lpsFin_cast_finEquiv] at hs
  have he : (∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2))=
      ((q:ℂ)^2-1)*lpsQuadraticE2Character q (-(γ 0 0:ZMod q)/(D:ZMod q)) := by
    simp_rw [lpsQuadraticEisensteinCuspGcd_weighted_of_dvd q γ D hC]
    exact hs
  rw [he] at ht
  simpa only [mul_assoc] using ht
end QEC.Coding.TannerLiftedProduct
