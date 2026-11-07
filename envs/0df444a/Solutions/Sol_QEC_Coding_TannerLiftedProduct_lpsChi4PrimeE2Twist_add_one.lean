-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:14:18.119608+00:00
-- url     : https://prove2.me/submissions/91c38bb5-48b6-4ddf-b37c-33fa82ad9092

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (z : ℍ) :
    lpsChi4PrimeE2Twist q ((1:ℝ) +ᵥ z)=lpsChi4PrimeE2Twist q z := by
  unfold lpsChi4PrimeE2Twist
  apply congrArg (fun w : ℂ => (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹*w)
  apply Finset.sum_congr rfl
  intro r hr
  have he : ((r.val:ℝ)/4) +ᵥ ((1:ℝ) +ᵥ z)=
      (1:ℝ) +ᵥ (((r.val:ℝ)/4) +ᵥ z) := by rw [←add_vadd,←add_vadd,add_comm]
  have hf := lpsQuadraticE2Twist_add_one q (((r.val:ℝ)/4) +ᵥ z)
  rw [←he] at hf
  exact congrArg (fun w : ℂ => lpsChi4E2Character (r.val:ZMod 4)*w) hf
end QEC.Coding.TannerLiftedProduct
