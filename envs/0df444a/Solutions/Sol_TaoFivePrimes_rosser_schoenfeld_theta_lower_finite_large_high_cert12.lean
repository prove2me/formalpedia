-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:08:16.630508+00:00
-- url     : https://prove2.me/submissions/ab7e13fb-d3bb-40c1-82ca-44f0e9f4aa91

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert11
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert111

theorem solution (n : Nat) (h1 : 88246776 <= n) (h2 : n <= 99999999) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((109937568534278953594 : Real) / 2 ^ 40 <= Chebyshev.theta (100000000 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert111
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert11 75778878 le_rfl (by norm_num)).2 n h1 h2
