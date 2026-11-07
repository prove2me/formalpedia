-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_coprime_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:36:04.609873+00:00
-- url     : https://prove2.me/submissions/a798239f-16ca-49e9-98a7-52b83d5485eb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_cusp_character_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspConstant_dilation

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q m : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hm : 0<m) (hmq : m.Coprime q) (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (lpsQuadraticE2Character q (m:ZMod q)*lpsQuadraticEisensteinCuspConstant q γ))) := by
  have h := lpsQuadraticE2Dilate_cusp_character_tendsto q m hq2 hm γ
  rw [lpsQuadraticEisensteinCuspConstant_dilation q m hm hmq γ] at h
  exact h
end QEC.Coding.TannerLiftedProduct
