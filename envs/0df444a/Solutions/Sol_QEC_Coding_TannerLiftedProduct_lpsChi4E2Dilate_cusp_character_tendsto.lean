-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Dilate_cusp_character_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:21.973893+00:00
-- url     : https://prove2.me/submissions/c95dfa13-1d0c-4113-9cf8-a01afbf417a9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilation_weightedCuspGcd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_cusp_character_tendsto


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        lpsChi4EisensteinCuspConstant (lpsEisensteinDilationCuspMatrix m hm γ))) := by
  have ht := lpsChi4E2Dilate_cusp_tendsto m hm γ
  have he := tendsto_nhds_unique (lpsChi4E2Twist_cusp_gcd_tendsto
    (lpsEisensteinDilationCuspMatrix m hm γ))
    (lpsChi4E2Twist_cusp_character_tendsto (lpsEisensteinDilationCuspMatrix m hm γ))
  have hs := lpsEisensteinDilation_weightedCuspGcd 4 m hm γ
    (fun r => lpsChi4E2Character (r.val:ZMod 4))
  norm_num only [Nat.cast_ofNat] at hs ht he
  rw [hs] at ht
  rw [mul_left_comm (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹
    ((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2),he] at ht
  exact ht
end QEC.Coding.TannerLiftedProduct
