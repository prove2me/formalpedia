-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.advantage_sign
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:21:45.240979+00:00
-- url     : https://prove2.me/submissions/dbdffd0b-3d20-4045-891c-e29496457659

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority

open TheoryOfGames.SimpleGames in
theorem solution {n : ℕ} (w : Fin n → ℝ) (hB : SatisfiesB w) (S : Finset (Fin n)) :
    (0 < advantage w S ↔ S ∈ weightedW w) ∧
    (advantage w S < 0 ↔ Sᶜ ∈ weightedW w) ∧
    advantage w S ≠ 0 := by
  have hc : ∑ i ∈ Sᶜ, w i + ∑ i ∈ S, w i = ∑ i, w i := Finset.sum_compl_add_sum S w
  have hne := hB.2 S
  simp only [advantage, weightedW, Set.mem_setOf_eq]
  refine ⟨⟨fun h => by linarith, fun h => by linarith⟩,
    ⟨fun h => by linarith, fun h => by linarith⟩, fun h => hne (by linarith)⟩
