-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite_low
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:08:12.581952+00:00
-- url     : https://prove2.me/submissions/465c0a67-4abd-4ccd-9bfd-b659dc3819a2

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_integer_endpoint_certificate_low
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_floor_envelope_low

theorem solution (t : Real) (h1 : 1420 <= t) (h2 : t <= 10 ^ 4) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  have htpos : (0 : Real) <= t := by linarith
  let n : Nat := Nat.floor t
  have hnlo : 1420 <= n := by
    dsimp [n]
    exact (Nat.le_floor_iff htpos).2 h1
  have hnhi : n <= 10000 := by
    dsimp [n]
    have hfloor : (Nat.floor t : Real) <= t := Nat.floor_le htpos
    exact_mod_cast (le_trans hfloor h2)
  have henv := TaoFivePrimes.rosser_schoenfeld_theta_lower_floor_envelope_low t h1 h2
  have hcert := TaoFivePrimes.rosser_schoenfeld_theta_lower_integer_endpoint_certificate_low n hnlo hnhi
  rw [Chebyshev.theta_eq_theta_coe_floor]
  exact lt_of_le_of_lt (by simpa [n] using henv) (by simpa [n] using hcert)
