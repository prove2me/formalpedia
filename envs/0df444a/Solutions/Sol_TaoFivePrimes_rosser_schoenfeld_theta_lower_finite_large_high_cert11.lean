-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:01:39.035529+00:00
-- url     : https://prove2.me/submissions/fcddb947-c41b-4a3c-97c6-f3e709ae9631

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert10
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert110

theorem solution (n : Nat) (h1 : 75778878 <= n) (h2 : n <= 88246775) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((97017863526510611905 : Real) / 2 ^ 40 <= Chebyshev.theta (88246776 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert110
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert10 63504866 le_rfl (by norm_num)).2 n h1 h2
