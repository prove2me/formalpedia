-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_nonZeroDivisors_of_not_mem_minimalPrimes_5ade1a33ecea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:57:32.639958+00:00
-- url     : https://prove2.me/submissions/9ac2d73d-94d5-4622-91dd-e1d2d946c65c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_minimalPrimes_of_mem_associatedPrimes_8f7461711774

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B] {y : B}
    (hy : ∀ p ∈ minimalPrimes B, y ∉ p) : y ∈ nonZeroDivisors B := by
  by_contra h
  have h' : y ∈ (nonZeroDivisors B : Set B)ᶜ := h
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.mem_iUnion₂] at h'
  obtain ⟨p, hp, hyp⟩ := h'
  exact hy p (mem_minimalPrimes_of_mem_associatedPrimes hp) hyp
end GroundTheory.Heights₂.Heights
