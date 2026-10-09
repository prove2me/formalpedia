-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:30:21.856537+00:00
-- url     : https://prove2.me/submissions/6466788e-b612-4059-8cd1-298106d1d58b

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert5
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert105

theorem solution (n : Nat) (h1 : 24178658 <= n) (h2 : n <= 33451167) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((36776160404945376298 : Real) / 2 ^ 40 <= Chebyshev.theta (33451168 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert105
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert5 16201780 le_rfl (by norm_num)).2 n h1 h2
