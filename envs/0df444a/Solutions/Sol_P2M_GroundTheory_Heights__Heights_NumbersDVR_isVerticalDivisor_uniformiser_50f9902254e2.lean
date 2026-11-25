-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_uniformiser_50f9902254e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:20.842471+00:00
-- url     : https://prove2.me/submissions/cb6443e1-3938-4fad-8c57-592e74021471

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_one_e110294ad3db

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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (H : Ideal (MRing ι O)) [H.IsPrime]
    (hϖ : (C ϖ : MRing ι O) ∉ H) :
    IsVerticalDivisor H ϖ 0 (C ϖ) 1 where
  degrees := ⟨0, 0, isWeightedHomogeneous_C _ _, isWeightedHomogeneous_one _ _, by
    funext k; simp⟩
  num_not_mem := hϖ
  den_not_mem := Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)
  vertical := by
    intro W hW
    unfold ratDiv at hW
    rw [divCycle_one, sub_zero] at hW
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    · exact absurd rfl hW
  unit_off_special := by
    intro W hW _ _ hϖW
    refine ⟨1, C ϖ, ?_, hϖW, ?_⟩
    · exact (Ideal.ne_top_iff_one W).mp hW.ne_top
    · rw [one_mul, mul_one, sub_self]
      exact H.zero_mem
end GroundTheory.Heights₂.Heights.NumbersDVR
