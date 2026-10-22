-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.never_dominates_self
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:11.130576+00:00
-- url     : https://prove2.me/submissions/95ada988-906b-4646-8db8-98b3029295c6

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution

set_option autoImplicit false
open TheoryOfGames.ThreePerson

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (α : Fin n → ℝ)
    (hα : IsImputation v α) : ¬ Dominates v α α := by
  rintro ⟨S, hS, _, hlt⟩
  obtain ⟨i, hi⟩ := hS
  exact lt_irrefl _ (hlt i hi)
