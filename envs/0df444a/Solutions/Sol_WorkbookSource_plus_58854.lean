-- Prove2me | solution 1 for WorkbookSource.plus_58854
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:41:51.963348+00:00
-- url     : https://prove2.me/submissions/2729546a-09f4-44cf-b7c0-b4211b9ab924

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + x^3 * z^3)   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6 + 3*x^4*y^2 + 3*x^4*z^2 - 8*x^3*y^3 - 8*x^3*z^3 + 3*x^2*y^4 + 6*x^2*y^2*z^2 + 3*x^2*z^4 + y^6 + 3*y^4*z^2 - 8*y^3*z^3 + 3*y^2*z^4 + z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * x^6 + (12 : ℝ) * x^5 * (y - x)^1 + (6 : ℝ) * x^5 * (z - y)^1 + (30 : ℝ) * x^4 * (y - x)^2 + (30 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (15 : ℝ) * x^4 * (z - y)^2 + (32 : ℝ) * x^3 * (y - x)^3 + (48 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (72 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (28 : ℝ) * x^3 * (z - y)^3 + (12 : ℝ) * x^2 * (y - x)^4 + (24 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (96 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (84 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (21 : ℝ) * x^2 * (z - y)^4 + (48 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (72 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (36 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (6 : ℝ) * x^1 * (z - y)^5 + (12 : ℝ) * (y - x)^4 * (z - y)^2 + (24 : ℝ) * (y - x)^3 * (z - y)^3 + (18 : ℝ) * (y - x)^2 * (z - y)^4 + (6 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6 + 3*x^4*y^2 + 3*x^4*z^2 - 8*x^3*y^3 - 8*x^3*z^3 + 3*x^2*y^4 + 6*x^2*y^2*z^2 + 3*x^2*z^4 + y^6 + 3*y^4*z^2 - 8*y^3*z^3 + 3*y^2*z^4 + z^6) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux0 x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux0 y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + x^3 * z^3)) := @solution
#print axioms solution
