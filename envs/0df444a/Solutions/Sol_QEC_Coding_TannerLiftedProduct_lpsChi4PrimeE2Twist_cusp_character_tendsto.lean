-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_cusp_character_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:19:25.166658+00:00
-- url     : https://prove2.me/submissions/55850b91-e95c-449f-b880-b0912a732619

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_cusp_character_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_character_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeEisensteinCuspGcd_weighted
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
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
    (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsChi4EisensteinCuspConstant γ*lpsQuadraticEisensteinCuspConstant q γ)) := by
  have ht := lpsChi4PrimeE2Dilate_cusp_tendsto q 1 (by decide) γ
  simp only [lpsChi4PrimeE2Dilate_one,Nat.cast_one,mul_one,one_pow] at ht
  have he4 := tendsto_nhds_unique (lpsChi4E2Twist_cusp_gcd_tendsto γ)
    (lpsChi4E2Twist_cusp_character_tendsto γ)
  have heq := tendsto_nhds_unique (lpsQuadraticE2Twist_cusp_gcd_tendsto q γ)
    (lpsQuadraticE2Twist_cusp_character_tendsto q hq2 γ)
  let v4 (r : Fin 4) : ℂ := lpsChi4E2Character (r.val:ZMod 4)*
    ((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0):ℂ)^2/(4:ℂ)^2)
  let vq (a : Fin q) : ℂ := lpsQuadraticE2Character q (a.val:ZMod q)*
    ((Int.gcd ((q:ℤ)*γ 0 0+(a.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2)
  let vk (r : Fin 4) (a : Fin q) : ℂ := lpsChi4E2Character (r.val:ZMod 4)*
    lpsQuadraticE2Character q (a.val:ZMod q)*
    ((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
      (((4*q:ℕ):ℤ)*γ 1 0):ℂ)^2/((4*q:ℕ):ℂ)^2)
  have hv (r : Fin 4) (a : Fin q) : vk r a=v4 r*vq a :=
    lpsChi4PrimeEisensteinCuspGcd_weighted q hq2 γ r a
  have hs : (∑ r : Fin 4,∑ a : Fin q,vk r a)=
      (∑ r : Fin 4,v4 r)*(∑ a : Fin q,vq a) := by
    simp_rw [hv,←Finset.mul_sum]
    rw [Finset.sum_mul]
  have hf : (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
        ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
          ∑ a : Fin q,lpsQuadraticE2Character q (a.val:ZMod q)*
            ((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
              (((4*q:ℕ):ℤ)*γ 1 0):ℂ)^2/((4*q:ℕ):ℂ)^2)))=
      ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹)*
        (∑ r : Fin 4,∑ a : Fin q,vk r a) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [vk]
    ring
  have he : ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
      (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹)*
      (∑ r : Fin 4,∑ a : Fin q,vk r a)=
      lpsChi4EisensteinCuspConstant γ*lpsQuadraticEisensteinCuspConstant q γ := by
    rw [hs,show ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
        (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹)*
        ((∑ r : Fin 4,v4 r)*(∑ a : Fin q,vq a))=
        ((gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*(∑ r : Fin 4,v4 r))*
          ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹*(∑ a : Fin q,vq a)) by ring]
    exact congrArg₂ (·*·) he4 heq
  rw [hf,he] at ht
  exact ht
end QEC.Coding.TannerLiftedProduct
