-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Dilate_cusp_character_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:23.499498+00:00
-- url     : https://prove2.me/submissions/68fb60be-3832-4067-b117-f1cbf3f8220c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilation_weightedCuspGcd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_character_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_gcd_tendsto


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q m : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (hm : 0<m) (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Dilate q m hm ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        lpsQuadraticEisensteinCuspConstant q (lpsEisensteinDilationCuspMatrix m hm γ))) := by
  have ht := lpsQuadraticE2Dilate_cusp_tendsto q m hm γ
  have he := tendsto_nhds_unique (lpsQuadraticE2Twist_cusp_gcd_tendsto q
    (lpsEisensteinDilationCuspMatrix m hm γ))
    (lpsQuadraticE2Twist_cusp_character_tendsto q hq2 (lpsEisensteinDilationCuspMatrix m hm γ))
  rw [lpsEisensteinDilation_weightedCuspGcd q m hm γ
    (fun r => lpsQuadraticE2Character q (r.val:ZMod q))] at ht
  rw [mul_left_comm (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹
    ((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2),he] at ht
  exact ht
end QEC.Coding.TannerLiftedProduct
