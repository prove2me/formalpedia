-- Prove2me | solution 1 for QZeroSum19.GK.fixed_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:23:35.540857+00:00
-- url     : https://prove2.me/submissions/1c6c34c8-a956-4a84-96fa-05758cf09665

import Mathlib
set_option autoImplicit false

theorem solution (n m : ℕ) (δ ε : ℝ) (hε : 0 < ε) (t : ℕ) (ht : 0 < t) :
    (Real.log ((n : ℝ) * m / δ) + 3 * t * ε ^ 2 / 16) / (t * ε / 4) =
        3 / 4 * ε + 4 * Real.log ((n : ℝ) * m / δ) / (t * ε) ∧
      (16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 ≤ t →
        (Real.log ((n : ℝ) * m / δ) + 3 * t * ε ^ 2 / 16) / (t * ε / 4) ≤ ε) := by
  generalize Real.log ((n : ℝ) * m / δ) = L
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hid : (L + 3 * t * ε ^ 2 / 16) / (t * ε / 4) = 3 / 4 * ε + 4 * L / (t * ε) := by
    field_simp
    ring
  refine ⟨hid, fun h => ?_⟩
  rw [hid]
  have h1 : 16 * L ≤ t * ε ^ 2 := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp h
    linarith
  have h2 : 4 * L / (t * ε) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith
