-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_floor_step
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-27T13:10:37.933585+00:00
-- url     : https://prove2.me/submissions/88152563-33e2-4bea-8afc-7323809a7a1f

import Mathlib.NumberTheory.Chebyshev

/-- For `10^6 <= t <= 10^8` the function `x - 2 sqrt x` at `t` is strictly below its value at the
next integer `floor t + 1`, the right endpoint of the interval on which `Chebyshev.theta`
is constant. -/
theorem solution (t : Real) (h1 : 10 ^ 6 <= t) (h2 : t <= 10 ^ 8) :
    t - 2 * Real.sqrt t < ((Nat.floor t : Real) + 1) - 2 * Real.sqrt ((Nat.floor t : Real) + 1) := by
  have ht0 : (0 : Real) ≤ t := by linarith
  have ht1 : (1 : Real) ≤ t := by linarith
  have htu : t < (Nat.floor t : Real) + 1 := Nat.lt_floor_add_one t
  have hy1 : (0 : Real) ≤ (Nat.floor t : Real) + 1 := by
    have : (0 : Real) ≤ (Nat.floor t : Real) := Nat.cast_nonneg _
    linarith
  have hs : Real.sqrt t < Real.sqrt ((Nat.floor t : Real) + 1) :=
    Real.sqrt_lt_sqrt (by linarith) htu
  have h1s : (1 : Real) ≤ Real.sqrt t := by
    rw [show (1 : Real) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ht1
  have et := Real.sq_sqrt (by linarith : (0 : Real) ≤ t)
  have ey := Real.sq_sqrt hy1
  nlinarith [mul_pos (sub_pos.2 hs)
    (by linarith : (0 : Real) < Real.sqrt ((Nat.floor t : Real) + 1) + Real.sqrt t - 2)]
