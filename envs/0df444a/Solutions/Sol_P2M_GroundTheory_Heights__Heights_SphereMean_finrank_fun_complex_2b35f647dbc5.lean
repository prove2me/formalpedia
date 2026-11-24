-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_finrank_fun_complex_2b35f647dbc5
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:40:17.286944+00:00
-- url     : https://prove2.me/submissions/c2b0d360-57b7-451f-b5f8-4a091f476617

import Mathlib


theorem solution (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  simp [Module.finrank_pi_fintype,Complex.finrank_real_complex,Nat.mul_comm]
