-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:55:41.40732+00:00
-- url     : https://prove2.me/submissions/733420c4-073e-4bba-a70b-9d06a22780d4

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert9
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert109

theorem solution (n : Nat) (h1 : 63504866 <= n) (h2 : n <= 75778877) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((83312136760431823633 : Real) / 2 ^ 40 <= Chebyshev.theta (75778878 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert109
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert9 52873594 le_rfl (by norm_num)).2 n h1 h2
