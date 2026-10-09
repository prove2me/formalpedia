-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:17:29.331355+00:00
-- url     : https://prove2.me/submissions/96b35846-b409-4d3c-a25b-e1b2f747faa3

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert3
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert103

theorem solution (n : Nat) (h1 : 9784043 <= n) (h2 : n <= 16201779) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((17808210448403255952 : Real) / 2 ^ 40 <= Chebyshev.theta (16201780 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert103
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert3 4513110 le_rfl (by norm_num)).2 n h1 h2
