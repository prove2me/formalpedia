-- Prove2me | solution 1 for WorkbookSource.plus_18871
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:30:00.949245+00:00
-- url     : https://prove2.me/submissions/26707ac5-7863-4079-a4b3-c4088c46ba8c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x^2 * (x^2 - y^2) * (x^2 - z^2) + y^2 * (y^2 - z^2) * (y^2 - x^2) + z^2 * (z^2 - x^2) * (z^2 - y^2) ≥ 8 * (y - z)^2 * (z - x)^2 * (x - y)^2   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6 - 9*x^4*y^2 + 16*x^4*y*z - 9*x^4*z^2 + 16*x^3*y^3 - 16*x^3*y^2*z - 16*x^3*y*z^2 + 16*x^3*z^3 - 9*x^2*y^4 - 16*x^2*y^3*z + 51*x^2*y^2*z^2 - 16*x^2*y*z^3 - 9*x^2*z^4 + 16*x*y^4*z - 16*x*y^3*z^2 - 16*x*y^2*z^3 + 16*x*y*z^4 + y^6 - 9*y^4*z^2 + 16*y^3*z^3 - 9*y^2*z^4 + z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * x^4 * (y - x)^2 + (4 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (4 : ℝ) * x^4 * (z - y)^2 + (4 : ℝ) * x^3 * (y - x)^3 + (6 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (26 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (12 : ℝ) * x^3 * (z - y)^3 + (1 : ℝ) * x^2 * (y - x)^4 + (2 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (45 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (44 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (13 : ℝ) * x^2 * (z - y)^4 + (32 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (48 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (28 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (6 : ℝ) * x^1 * (z - y)^5 + (6 : ℝ) * (y - x)^2 * (z - y)^4 + (6 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6 - 9*x^4*y^2 + 16*x^4*y*z - 9*x^4*z^2 + 16*x^3*y^3 - 16*x^3*y^2*z - 16*x^3*y*z^2 + 16*x^3*z^3 - 9*x^2*y^4 - 16*x^2*y^3*z + 51*x^2*y^2*z^2 - 16*x^2*y*z^3 - 9*x^2*z^4 + 16*x*y^4*z - 16*x*y^3*z^2 - 16*x*y^2*z^3 + 16*x*y*z^4 + y^6 - 9*y^4*z^2 + 16*y^3*z^3 - 9*y^2*z^4 + z^6) := by
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
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), x^2 * (x^2 - y^2) * (x^2 - z^2) + y^2 * (y^2 - z^2) * (y^2 - x^2) + z^2 * (z^2 - x^2) * (z^2 - y^2) ≥ 8 * (y - z)^2 * (z - x)^2 * (x - y)^2) := @solution
#print axioms solution
