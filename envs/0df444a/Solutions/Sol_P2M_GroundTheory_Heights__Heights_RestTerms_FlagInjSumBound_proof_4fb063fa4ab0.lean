-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagInjSumBound_proof_4fb063fa4ab0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:04.066782+00:00
-- url     : https://prove2.me/submissions/cd35ff97-6fab-45b7-8ff2-9bea0c811245

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagInjSumBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagInjSumBound_finset_sum_bound_cc3c3372d6d6

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
open GroundTheory.Heights₂.Heights.RestTerms
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagInjSumBound
theorem _root_.solution : FlagInjSumBound.Statement := by
  intro N g hg
  classical
  set S := Finset.univ.image g with hSdef
  have hcard : S.card = N := by
    rw [hSdef, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i, g i = ∑ x ∈ S, x := by
    rw [hSdef, Finset.sum_image (fun i _ j _ h => hg h)]
  obtain ⟨h₁, h₂⟩ := FlagInjSumBound.finset_sum_bound S
  rw [hcard, Finset.sum_range_id] at h₁ h₂
  rw [hsum]
  refine ⟨h₁, fun heq i => ?_⟩
  have hi : g i ∈ S := Finset.mem_image_of_mem g (Finset.mem_univ i)
  exact Finset.mem_range.1 (h₂ heq hi)
end FlagInjSumBound
end GroundTheory.Heights₂.Heights.RestTerms
