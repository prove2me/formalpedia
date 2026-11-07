-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_cusp_character_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:43.038162+00:00
-- url     : https://prove2.me/submissions/1248bc9d-918a-4063-bd9a-f441f3e2b4b2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_unit_reduce
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4EisensteinCuspGcd_difference
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_not_both_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_values
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_sq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
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
theorem _root_.solution (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Twist ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsChi4EisensteinCuspConstant γ)) := by
  have ht := lpsChi4E2Twist_cusp_gcd_tendsto γ
  have hg1 := lpsEisensteinCuspGcd_unit_reduce 4 γ 1 (by norm_num)
  have hg3 := lpsEisensteinCuspGcd_unit_reduce 4 γ 3 (by norm_num)
  norm_num only [Int.natAbs_natCast,Nat.reducePow,Int.reducePow,one_mul] at hg1 hg3
  have hd := lpsChi4EisensteinCuspGcd_difference (γ 0 0) (γ 1 0)
    (lpsSL2Z_firstColumn_not_both_even γ)
  have he : (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
        ((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0):ℂ)^2/(4:ℂ)^2))=
      lpsChi4EisensteinCuspConstant γ := by
    rw [Fin.sum_univ_four]
    change (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹ *
      (lpsChi4E2Character 0*((Int.gcd (4*γ 0 0+0*γ 1 0) (4*γ 1 0):ℂ)^2/(4:ℂ)^2)+
       lpsChi4E2Character 1*((Int.gcd (4*γ 0 0+1*γ 1 0) (4*γ 1 0):ℂ)^2/(4:ℂ)^2)+
       lpsChi4E2Character 2*((Int.gcd (4*γ 0 0+2*γ 1 0) (4*γ 1 0):ℂ)^2/(4:ℂ)^2)+
       lpsChi4E2Character 3*((Int.gcd (4*γ 0 0+3*γ 1 0) (4*γ 1 0):ℂ)^2/(4:ℂ)^2))=_
    rw [lpsChi4E2Character_values.1,lpsChi4E2Character_values.2.1,
      lpsChi4E2Character_values.2.2.1,lpsChi4E2Character_values.2.2.2]
    simp only [zero_mul,zero_add,add_zero,one_mul,neg_one_mul]
    rw [hg1,hg3]
    rw [show (((Int.gcd (4*γ 0 0+γ 1 0) 16:ℕ):ℂ)^2/(4:ℂ)^2+
        -(((Int.gcd (4*γ 0 0+3*γ 1 0) 16:ℕ):ℂ)^2/(4:ℂ)^2))=
      (((Int.gcd (4*γ 0 0+γ 1 0) 16:ℕ):ℂ)^2-
        ((Int.gcd (4*γ 0 0+3*γ 1 0) 16:ℕ):ℂ)^2)/(4:ℂ)^2 by ring,hd]
    unfold lpsChi4EisensteinCuspConstant
    split_ifs with hc
    · have hs := lpsChi4E2Gauss_sq
      have hn := lpsChi4E2Gauss_ne_zero
      field_simp [hn]
      linear_combination -48*lpsChi4E2Character (((γ 0 0*(γ 1 0/4)):ℤ):ZMod 4)*hs
    · simp
  rw [he] at ht
  exact ht
end QEC.Coding.TannerLiftedProduct
