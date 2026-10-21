-- Prove2me | solution 1 for SlowConvergence.SteepestDescent.psi_mem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:40:15.749418+00:00
-- url     : https://prove2.me/submissions/b4296612-3743-41c8-a86f-d626dae11e0b

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data
import Definitions.Def_SlowConvergence_SteepestDescent_Hermite

set_option autoImplicit false
open SlowConvergence.SteepestDescent

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 < psi τ k ∧ psi τ k < 1 := by
  have hη : 0 < SlowConvergence.Newton.eta τ := by
    unfold SlowConvergence.Newton.eta
    apply div_pos hτ0; linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hexp : 0 < 1 / 2 + SlowConvergence.Newton.eta τ := by linarith
  unfold psi
  constructor
  · apply Real.rpow_pos_of_pos
    positivity
  · apply Real.rpow_lt_one (by positivity) _ hexp
    rw [div_lt_one (by positivity)]
    linarith
