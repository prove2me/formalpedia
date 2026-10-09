-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:37:06.539617+00:00
-- url     : https://prove2.me/submissions/9af85343-3d6f-4551-9d38-cc2261e66eee

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert6
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert106

theorem solution (n : Nat) (h1 : 33451168 <= n) (h2 : n <= 42031448) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((46205333685667793059 : Real) / 2 ^ 40 <= Chebyshev.theta (42031449 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert106
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert6 24178658 le_rfl (by norm_num)).2 n h1 h2
