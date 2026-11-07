-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_character_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:03:24.871829+00:00
-- url     : https://prove2.me/submissions/15b28293-5c17-4345-96cd-87c77f50d2cf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_not_dvd_tendsto_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_dvd_character_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_cusp_square_dvd_tendsto_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (lpsQuadraticEisensteinCuspConstant q γ)) := by
  unfold lpsQuadraticEisensteinCuspConstant
  by_cases hC : (q:ℤ)∣γ 1 0
  · rw [if_pos hC]
    let D : ℤ := γ 1 0/(q:ℤ)
    have hCD : γ 1 0=(q:ℤ)*D := (Int.mul_ediv_cancel_of_dvd hC).symm
    have hq : (q:ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    have hd : (q:ℤ)^2∣γ 1 0 ↔ (q:ℤ)∣D := by
      rw [hCD,pow_two,mul_dvd_mul_iff_left hq]
    by_cases h2 : (q:ℤ)^2∣γ 1 0
    · rw [if_pos h2]
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd D q).mpr (hd.mp h2)
      exact lpsQuadraticE2Twist_cusp_square_dvd_tendsto_zero q hq2 γ D hCD hz
    · rw [if_neg h2]
      have hn : (D:ZMod q)≠0 := by
        intro hz
        exact h2 (hd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd D q).mp hz))
      exact lpsQuadraticE2Twist_cusp_dvd_character_tendsto q hq2 γ D hCD hn
  · rw [if_neg hC]
    exact lpsQuadraticE2Twist_cusp_not_dvd_tendsto_zero q hq2 γ hC
end QEC.Coding.TannerLiftedProduct
