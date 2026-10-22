-- Prove2me | solution 1 for SlowConvergence.Newton.gradient_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:24:03.604424+00:00
-- url     : https://prove2.me/submissions/37c73896-c4f9-410f-80ec-916511502a9d

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

set_option autoImplicit false
open scoped RealInnerProductSpace

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    1 / 2 + SlowConvergence.Newton.eta τ = 1 / (2 - τ) ∧
      ∀ k : ℕ, (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ)) ≤ ‖SlowConvergence.Newton.gk τ k‖ := by
  have h2 : (2 : ℝ) - τ ≠ 0 := by intro h; linarith
  have h4 : (4 : ℝ) - 2 * τ ≠ 0 := by intro h; linarith
  have he : 1 / 2 + SlowConvergence.Newton.eta τ = 1 / (2 - τ) := by
    unfold SlowConvergence.Newton.eta
    field_simp
    ring
  refine ⟨he, fun k => ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmu : SlowConvergence.Newton.mu τ k = (1 / ((k : ℝ) + 1)) ^ (1 / (2 - τ)) := by
    unfold SlowConvergence.Newton.mu
    rw [he]
  have hnn : 0 ≤ SlowConvergence.Newton.mu τ k := by
    unfold SlowConvergence.Newton.mu
    exact Real.rpow_nonneg (by positivity) _
  have hc : ‖SlowConvergence.Newton.gk τ k 0‖ ≤ ‖SlowConvergence.Newton.gk τ k‖ :=
    PiLp.norm_apply_le _ 0
  have h0 : SlowConvergence.Newton.gk τ k 0 = -SlowConvergence.Newton.mu τ k := by
    simp [SlowConvergence.Newton.gk]
  rw [h0, norm_neg, Real.norm_of_nonneg hnn, hmu] at hc
  exact hc
