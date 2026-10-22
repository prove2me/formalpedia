-- Prove2me | solution 1 for SlowConvergence.ARC.gradient_formula
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:27:59.294243+00:00
-- url     : https://prove2.me/submissions/c9fdf5e9-6556-431e-a650-2f3e2e8a4ad2

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

set_option autoImplicit false
open SlowConvergence.ARC

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    eta τ = 2 * τ / (9 - 6 * τ) ∧ 0 < eta τ ∧ 2 / 3 + 2 * eta τ = 2 / (3 - 2 * τ) ∧
      ∀ k : ℕ, |gk τ k| = (1 / ((k : ℝ) + 1)) ^ (2 / (3 - 2 * τ)) := by
  have h3 : 0 < 3 - 2 * τ := by linarith
  have h9 : 0 < 9 - 6 * τ := by linarith
  have h3' : 3 - 2 * τ ≠ 0 := h3.ne'
  have h9' : 9 - 6 * τ ≠ 0 := h9.ne'
  have h96 : 9 - 6 * τ = 3 * (3 - 2 * τ) := by ring
  have e1 : eta τ = 2 * τ / (9 - 6 * τ) := by
    rw [h96]; unfold eta; field_simp; ring
  have e3 : 2 / 3 + 2 * eta τ = 2 / (3 - 2 * τ) := by
    rw [e1, h96]; field_simp; ring
  refine ⟨e1, ?_, e3, ?_⟩
  · rw [e1]; exact div_pos (by linarith) h9
  · intro k
    unfold gk
    rw [abs_neg, abs_of_nonneg (by positivity), e3]
