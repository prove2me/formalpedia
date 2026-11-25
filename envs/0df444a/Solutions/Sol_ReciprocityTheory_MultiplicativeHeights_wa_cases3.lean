-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_cases3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:05:55.63931+00:00
-- url     : https://prove2.me/submissions/dcd5ef0c-dc89-4ccb-ba7a-8b71e481f20f

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (i : Fin (n + 2)) :
    i = 0 ∨ i = Fin.last (n + 1) ∨ ∃ j : Fin n, i = (Fin.castSucc j).succ := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · exact Or.inl h
  · right
    induction j using Fin.lastCases with
    | last => left; simp
    | cast j => right; exact ⟨j, rfl⟩
end ReciprocityTheory.MultiplicativeHeights
