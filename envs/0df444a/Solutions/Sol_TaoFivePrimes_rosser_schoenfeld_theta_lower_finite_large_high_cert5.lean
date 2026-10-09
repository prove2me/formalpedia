-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:24:05.452856+00:00
-- url     : https://prove2.me/submissions/1a3ce0a0-9b02-436c-8678-295137518c73

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert4
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert104

theorem solution (n : Nat) (h1 : 16201780 <= n) (h2 : n <= 24178657) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((26578290012770846058 : Real) / 2 ^ 40 <= Chebyshev.theta (24178658 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert104
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert4 9784043 le_rfl (by norm_num)).2 n h1 h2
