-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Dilate_cusp_coprime_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:36:09.165591+00:00
-- url     : https://prove2.me/submissions/0549cedf-18fa-413a-866f-83379dffdb96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Dilate_cusp_character_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4EisensteinCuspConstant_dilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0<m)
    (hm4 : m.Coprime 4) (γ : SL(2,ℤ)) :
    Tendsto (lpsChi4E2Dilate m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (lpsChi4E2Character (m:ZMod 4)*lpsChi4EisensteinCuspConstant γ))) := by
  have h := lpsChi4E2Dilate_cusp_character_tendsto m hm γ
  rw [lpsChi4EisensteinCuspConstant_dilation m hm hm4 γ] at h
  exact h
end QEC.Coding.TannerLiftedProduct
