-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombSortShiftDistinct_proof_b5b0e4af78c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:32:24.846999+00:00
-- url     : https://prove2.me/submissions/b4a257d4-88b6-43b5-bdd0-7f5c032b523f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombSortShiftDistinct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Equiv
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombSortShiftDistinct
theorem _root_.solution : CombSortShiftDistinct.Statement := by
  intro m l hl q hq i j hij hqi hqj σ τ heq
  have hr := congrArg Set.range heq
  rw [σ.surjective.range_comp, τ.surjective.range_comp] at hr
  have hmem : l i ∈ Set.range (Function.update l j (l j - q)) :=
    ⟨i, by rw [Function.update_of_ne hij]⟩
  rw [← hr] at hmem
  obtain ⟨k, hk⟩ := hmem
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self] at hk
    omega
  · rw [Function.update_of_ne hki] at hk
    exact hki (hl hk)
end CombSortShiftDistinct
end GroundTheory.Heights₂.Heights.RestTerms
