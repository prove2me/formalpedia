-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:10:21.902311+00:00
-- url     : https://prove2.me/submissions/3da75221-20de-47ba-b290-42c8d9cbad59

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert2
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert102

theorem solution (n : Nat) (h1 : 4513110 <= n) (h2 : n <= 9784042) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((10753850669169348497 : Real) / 2 ^ 40 <= Chebyshev.theta (9784043 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert102
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert2 1202669 le_rfl (by norm_num)).2 n h1 h2
