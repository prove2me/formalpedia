-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_uniformiser_pow_mul_ba2bf2272261
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:00.549802+00:00
-- url     : https://prove2.me/submissions/ee663e1b-b261-4b08-877d-3d8d38066651

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByEffectiveDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IsVerticalDivisor_of_unit_off_special_da747d91115e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace IsVerticalDivisor
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {H : Ideal (MRing ι O)}
    [hH : H.IsPrime] {ϖ : O} (hϖ : (C ϖ : MRing ι O) ∉ H) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor H ϖ b f g) (n : ℕ) :
    IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
  · have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
      rw [← map_pow]
      exact isWeightedHomogeneous_C _ _
    have := h0.mul hf
    rwa [zero_add] at this
  · exact hH.mul_notMem (fun h => hϖ (hH.mem_of_pow_mem n h)) hD.num_not_mem
  · intro W hW hHW hrel hϖW
    obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hHW hrel hϖW
    refine ⟨u, C ϖ ^ n * v, hu, hW.mul_notMem (fun h => hϖW (hW.mem_of_pow_mem n h)) hv, ?_⟩
    have e : u * (C ϖ ^ n * f) - C ϖ ^ n * v * g = C ϖ ^ n * (u * f - v * g) := by ring
    rw [e]
    exact H.mul_mem_left _ huv
end IsVerticalDivisor
end GroundTheory.Heights₂.Heights.NumbersDVR
