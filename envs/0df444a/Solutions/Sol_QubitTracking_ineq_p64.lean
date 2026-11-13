-- Prove2me | solution 1 for QubitTracking.ineq_p64
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T16:15:54.197196+00:00
-- url     : https://prove2.me/submissions/8f0db40c-d2ab-41b0-ae11-826ac8554c26

import Mathlib

set_option autoImplicit false

/-- `1 − η^{2/γ} ≤ 2 log(1/η)/γ`, with the exponential rewriting of the real power. -/
theorem solution (η γ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hγ : 0 < γ) :
    1 - η ^ (2 / γ) = 1 - Real.exp (-(2 * Real.log (1 / η) / γ)) ∧
      1 - Real.exp (-(2 * Real.log (1 / η) / γ)) ≤ 2 * Real.log (1 / η) / γ := by
  constructor
  · rw [Real.rpow_def_of_pos hη]
    have harg : Real.log η * (2 / γ) = -(2 * Real.log (1 / η) / γ) := by
      rw [Real.log_div one_ne_zero hη.ne', Real.log_one]
      ring
    rw [harg]
  · have hlog : 0 ≤ Real.log (1 / η) := by
      apply Real.log_nonneg
      rw [one_div]
      exact (one_le_inv₀ hη).mpr hη1
    have ht : 0 ≤ 2 * Real.log (1 / η) / γ := div_nonneg (by nlinarith) hγ.le
    have h := Real.add_one_le_exp (-(2 * Real.log (1 / η) / γ))
    linarith
