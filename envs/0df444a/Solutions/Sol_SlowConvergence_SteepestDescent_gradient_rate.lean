-- Prove2me | solution 1 for SlowConvergence.SteepestDescent.gradient_rate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:40:16.832989+00:00
-- url     : https://prove2.me/submissions/f44eae54-0c24-4082-97df-1965f6e64015

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data

set_option autoImplicit false
open SlowConvergence.SteepestDescent

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    1 / (2 - τ) - 1 / 2 = SlowConvergence.Newton.eta τ ∧ 0 < SlowConvergence.Newton.eta τ ∧
      ∀ k : ℕ, |gk τ k| = (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ)) := by
  have h2 : (2 : ℝ) - τ ≠ 0 := by intro h; linarith
  have h4 : (4 : ℝ) - 2 * τ ≠ 0 := by intro h; linarith
  have hη : 1 / (2 - τ) - 1 / 2 = SlowConvergence.Newton.eta τ := by
    unfold SlowConvergence.Newton.eta
    field_simp
    ring
  refine ⟨hη, ?_, ?_⟩
  · unfold SlowConvergence.Newton.eta
    apply div_pos hτ0; linarith
  · intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have he : 1 / 2 + SlowConvergence.Newton.eta τ = 1 / (2 - τ) := by linarith
    unfold gk
    rw [abs_neg, abs_of_nonneg (Real.rpow_nonneg (by positivity) _), he]
