-- Prove2me | solution 1 for TongString.lorentz_anomaly_coefficient_vanishes_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T14:09:06.948325+00:00
-- url     : https://prove2.me/submissions/d6ba6414-69d3-4637-a119-6288ee615854

import Mathlib

theorem solution (D : ℕ) (a : ℝ) :
    (∀ n : ℕ, 0 < n →
        (((D : ℝ) - 2) / 24 - 1) * n + 1 / (n : ℝ) * (a - ((D : ℝ) - 2) / 24) = 0) ↔
      (D = 26 ∧ a = 1) := by
  constructor
  · intro h
    have h1 := h 1 one_pos
    have h2 := h 2 two_pos
    push_cast at h1 h2
    have hD : (D : ℝ) = 26 := by linarith
    refine ⟨by exact_mod_cast hD, ?_⟩
    rw [hD] at h1
    linarith
  · rintro ⟨rfl, rfl⟩ n _
    norm_num
