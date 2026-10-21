-- Prove2me | solution 1 for SlowConvergence.Newton.psi_mem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:09:08.475916+00:00
-- url     : https://prove2.me/submissions/102d3c83-6700-4ba0-824c-ed64b8e9ca52

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_Newton_Pieces

set_option autoImplicit false
open scoped RealInnerProductSpace

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 < |SlowConvergence.SteepestDescent.psi τ k| ∧ |SlowConvergence.SteepestDescent.psi τ k| < 1 := by
  have hη : 0 < SlowConvergence.Newton.eta τ := by
    unfold SlowConvergence.Newton.eta
    apply div_pos hτ0; linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hexp : 0 < 1 / 2 + SlowConvergence.Newton.eta τ := by linarith
  have h0 : 0 < SlowConvergence.SteepestDescent.psi τ k := by
    unfold SlowConvergence.SteepestDescent.psi
    apply Real.rpow_pos_of_pos
    positivity
  have h1 : SlowConvergence.SteepestDescent.psi τ k < 1 := by
    unfold SlowConvergence.SteepestDescent.psi
    apply Real.rpow_lt_one (by positivity) _ hexp
    rw [div_lt_one (by positivity)]
    linarith
  rw [abs_of_pos h0]
  exact ⟨h0, h1⟩
