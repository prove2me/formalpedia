-- Prove2me | solution 1 for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-17T05:05:09.906842+00:00
-- url     : https://prove2.me/submissions/2ea72ff2-f9e0-4286-87ca-1a0a0ee543a0

import Theorems.Thm_dusart_theta_mesh_analytic_completion
import Theorems.Thm_dusart_theta_mesh_complete_upper_chain
theorem solution (n : ℕ) (hn : 32 ≤ n) (hcap : n ≤ Nat.ceil (16 * Real.exp 23)) :
    let a : ℝ := (n : ℝ) / 16
    let b : ℝ := ((n : ℝ) + 1) / 16
    |Chebyshev.theta a - a| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 ∧
      |Chebyshev.theta a - b| ≤ (1513 / 10 : ℝ) * a / (Real.log b)^4 :=
  dusart_theta_mesh_analytic_completion dusart_theta_mesh_complete_upper_chain n hn hcap
