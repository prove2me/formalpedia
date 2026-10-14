-- Prove2me | solution 1 for PersistClust.Count.mult_off_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T19:47:33.05482+00:00
-- url     : https://prove2.me/submissions/d2db5a7b-4f5a-498a-ab49-732f80afe235

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem solution (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r) := by
  intro p hp
  by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
  · rw [mult, if_pos h1] at hp
    by_cases h2 : p.2 = ⊥
    · rw [if_pos h2] at hp
      rw [h2]
      exact bot_lt_iff_ne_bot.mpr h1.1
    · rw [if_neg h2] at hp
      by_cases h3 : p.2 < p.1
      · exact h3
      · rw [if_neg h3] at hp
        exact (hp rfl).elim
  · rw [mult, if_neg h1] at hp
    exact (hp rfl).elim
