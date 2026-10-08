-- Prove2me | solution 1 for RobustUncLP.WorstCase.rfeasible_iff_rowwise
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:58:13.292306+00:00
-- url     : https://prove2.me/submissions/7799cc37-d549-4ab9-8665-5d22728f4de5

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting

set_option autoImplicit false

open Matrix RobustUncLP.WorstCase in
theorem solution {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (f : Fin n → ℝ) :
    ∀ x : Fin n → ℝ, x ∈ robustFeas U f ↔
      (∀ i : Fin m, ∀ a ∈ rowProj U i, 0 ≤ a ⬝ᵥ x) ∧ f ⬝ᵥ x = 1 := by
  intro x
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rintro i a ⟨A, hA, rfl⟩
    have := h1 A hA i
    simpa [Matrix.mulVec] using this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    intro A hA i
    have := h1 i (A i) ⟨A, hA, rfl⟩
    simpa [Matrix.mulVec] using this
