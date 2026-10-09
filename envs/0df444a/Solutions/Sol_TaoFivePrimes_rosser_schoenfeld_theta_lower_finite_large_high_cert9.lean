-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:49:54.145233+00:00
-- url     : https://prove2.me/submissions/8fb301ef-eb9c-4a9e-a094-c58a35618315

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert8
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert108

theorem solution (n : Nat) (h1 : 52873594 <= n) (h2 : n <= 63504865) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((69813481915685380291 : Real) / 2 ^ 40 <= Chebyshev.theta (63504866 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert108
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert8 42031449 le_rfl (by norm_num)).2 n h1 h2
