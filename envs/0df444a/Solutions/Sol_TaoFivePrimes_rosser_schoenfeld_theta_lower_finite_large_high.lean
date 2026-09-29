-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-27T13:11:09.049848+00:00
-- url     : https://prove2.me/submissions/9943089d-8db9-4181-a4f3-06e8b1245d6f

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_floor_step
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_integer_certificate

/-- On `[10^6, 10^8]` the Rosser--Schoenfeld lower bound `t - 2 sqrt t < theta t` follows from
the analytic floor step and the integer endpoint certificate on `[10^6, 10^8]`. -/
theorem solution (t : Real) (h1 : 10 ^ 6 <= t) (h2 : t <= 10 ^ 8) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by
  have ht0 : (0 : Real) ≤ t := by linarith
  have hlt1 : 10 ^ 6 ≤ Nat.floor t := by
    apply Nat.le_floor
    push_cast
    linarith
  have hlt2 : Nat.floor t ≤ 10 ^ 8 := by
    have h := Nat.floor_le ht0
    have h' : ((Nat.floor t : Nat) : Real) ≤ ((10 ^ 8 : Nat) : Real) := by
      push_cast
      linarith
    exact_mod_cast h'
  have hA := TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_floor_step t h1 h2
  have hB := TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_integer_certificate
    (Nat.floor t) hlt1 hlt2
  rw [Chebyshev.theta_eq_theta_coe_floor t]
  exact lt_of_lt_of_le hA hB
