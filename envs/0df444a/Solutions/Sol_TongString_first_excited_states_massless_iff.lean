-- Prove2me | solution 1 for TongString.first_excited_states_massless_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T13:40:04.198139+00:00
-- url     : https://prove2.me/submissions/5b269a84-1b11-48bb-9d2a-8c546e4f6c85

import Mathlib

theorem solution (α' : ℝ) (hα' : 0 < α') (D : ℕ) :
    4 / α' * (1 - ((D : ℝ) - 2) / 24) = 0 ↔ D = 26 := by
  constructor
  · intro h
    have h1 : (4 / α') ≠ 0 := by positivity
    have h2 : 1 - ((D : ℝ) - 2) / 24 = 0 := by
      rcases mul_eq_zero.mp h with h3 | h3
      · exact absurd h3 h1
      · exact h3
    have h4 : (D : ℝ) = 26 := by linarith
    exact_mod_cast h4
  · rintro rfl
    norm_num
