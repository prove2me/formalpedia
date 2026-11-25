-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookDimensionSum_proof_2d5ba473993f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:37:31.261903+00:00
-- url     : https://prove2.me/submissions/f75f673a-5d6c-430e-820c-d541cee3f16a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookDimensionSum

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
open Finset Comb
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace HookDimensionSum
theorem _root_.solution (h1 : CombTableEqWords.Statement)
    (h2 : CombHookShapeFacts.Statement) (h3 : CombHookCount.Statement) :
    HookDimensionSum.Statement := by
  intro k hk
  have hterm : ∀ l ∈ Finset.range k,
      numStandardTable (hookShape k k l) = (k - 1).choose l := by
    intro l hl
    have hl' : l < k := Finset.mem_range.mp hl
    obtain ⟨hanti, hsum⟩ := h2 k k l hl' le_rfl
    rw [h1 k (hookShape k k l) hanti, hsum]
    exact h3 k k l hl' le_rfl
  rw [Finset.sum_congr rfl hterm]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simpa using Nat.sum_range_choose n
end HookDimensionSum
end GroundTheory.Heights₂.Heights.RestTerms
