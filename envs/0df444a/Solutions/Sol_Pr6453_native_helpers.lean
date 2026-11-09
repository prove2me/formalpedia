-- Prove2me | solution 1 for Pr6453.native_helpers
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T18:35:19.558248+00:00
-- url     : https://prove2.me/submissions/34cd7b23-d4d7-40e5-bc19-b7a07c4748d5

/-
PR #6453: the enumerated native helpers.
-/
import Definitions.Def_Pr6453_Word
import Definitions.Def_Pr6453_WordNative

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pr6453

theorem native_helpers :
    helperRanks.length = 562 ∧ rankCount 1 = 14 ∧ rankCount 2 = 8 ∧ rankCount 3 = 4 ∧
      rankCount 4 = 107 ∧ rankCount 5 = 15 ∧ rankCount 6 = 3 ∧ rankCount 7 = 9 ∧
      rankCount 8 = 39 ∧ rankCount 9 = 363 ∧ distinctMaps = 2941 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, rfl⟩

end Pr6453

/-- **The enumerated native helpers of PR #6453.** -/
theorem solution :
    Pr6453.helperRanks.length = 562 ∧ Pr6453.rankCount 1 = 14 ∧ Pr6453.rankCount 2 = 8 ∧
      Pr6453.rankCount 3 = 4 ∧ Pr6453.rankCount 4 = 107 ∧ Pr6453.rankCount 5 = 15 ∧
      Pr6453.rankCount 6 = 3 ∧ Pr6453.rankCount 7 = 9 ∧ Pr6453.rankCount 8 = 39 ∧
      Pr6453.rankCount 9 = 363 ∧ Pr6453.distinctMaps = 2941 :=
  Pr6453.native_helpers
