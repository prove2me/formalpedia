-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T00:43:23.744285+00:00
-- url     : https://prove2.me/submissions/df168d0d-0c88-489c-a1db-1bdd05e5b619

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert7
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert107

theorem solution (n : Nat) (h1 : 42031449 <= n) (h2 : n <= 52873593) : (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\ ((58127927172669014209 : Real) / 2 ^ 40 <= Chebyshev.theta (52873594 : Real)) := by
  exact TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert107
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert7 33451168 le_rfl (by norm_num)).2 n h1 h2
