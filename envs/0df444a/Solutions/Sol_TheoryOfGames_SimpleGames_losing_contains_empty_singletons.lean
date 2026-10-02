-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.losing_contains_empty_singletons
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:26:22.045278+00:00
-- url     : https://prove2.me/submissions/aa1c1e16-a010-4f2a-995c-34ce53ba50d3

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

open TheoryOfGames.SimpleGames in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) :
    ∅ ∈ losingSets v ∧ ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ losingSets v := by
  refine ⟨?_, fun i => ?_⟩
  · show v ∅ = ∑ k ∈ (∅ : Finset (Fin n)), v {k}
    rw [Finset.sum_empty]
    exact hv.1
  · show v {i} = ∑ k ∈ ({i} : Finset (Fin n)), v {k}
    rw [Finset.sum_singleton]
