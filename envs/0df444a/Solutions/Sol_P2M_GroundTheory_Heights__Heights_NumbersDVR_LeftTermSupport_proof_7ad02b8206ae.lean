-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LeftTermSupport_proof_7ad02b8206ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:25.028803+00:00
-- url     : https://prove2.me/submissions/d667ac8f-89c3-4157-b54a-34645dc57a89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleNeZeroFacts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_ne_zero_facts_17d796702cc2

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
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LeftTermSupport
theorem _root_.solution : LeftTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs G U hU
  by_contra hne
  apply hU
  have hG : ratDiv P f g G ≠ 0 := left_ne_zero_of_mul hne
  have hU' : divCycle G s U ≠ 0 := right_ne_zero_of_mul hne
  have hϖG : (C ϖ : MRing ι O) ∈ G := hD.vertical G hG
  obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
  have hGfacts : P ≤ G ∧ IsMultiHomogIdeal G := by
    have : divCycle P f G ≠ 0 ∨ divCycle P g G ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hG (by unfold ratDiv; rw [h.1, h.2, sub_zero])
    rcases this with h | h
    · exact (divCycle_ne_zero_facts hP hf h).2.2
    · exact (divCycle_ne_zero_facts hP hg h).2.2
  obtain ⟨hUp, hUr, hGU, hUm⟩ := divCycle_ne_zero_facts hGfacts.2 hs hU'
  exact ⟨hUp, hUm, hUr, hGU hϖG, le_trans hGfacts.1 hGU⟩
end LeftTermSupport
end GroundTheory.Heights₂.Heights.NumbersDVR
