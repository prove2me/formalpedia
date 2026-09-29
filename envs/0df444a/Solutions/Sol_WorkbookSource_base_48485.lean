-- Prove2me | solution 1 for WorkbookSource.base_48485
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:24.87295+00:00
-- url     : https://prove2.me/submissions/d3f35c2e-890e-4f18-acbd-c4e872c36ec1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 8 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 ≥ 9 * (x + y) * (y + z) * (z + x) * (x ^ 3 + y ^ 3 + z ^ 3)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (8*x^6 - 9*x^5*y - 9*x^5*z + 15*x^4*y^2 - 18*x^4*y*z + 15*x^4*z^2 - 9*x^3*y^2*z - 9*x^3*y*z^2 + 15*x^2*y^4 - 9*x^2*y^3*z + 48*x^2*y^2*z^2 - 9*x^2*y*z^3 + 15*x^2*z^4 - 9*x*y^5 - 18*x*y^4*z - 9*x*y^3*z^2 - 9*x*y^2*z^3 - 18*x*y*z^4 - 9*x*z^5 + 8*y^6 - 9*y^5*z + 15*y^4*z^2 + 15*y^2*z^4 - 9*y*z^5 + 8*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * x^4 * (y - x)^2 + (18 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (18 : ℝ) * x^4 * (z - y)^2 + (62 : ℝ) * x^3 * (y - x)^3 + (93 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (51 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (10 : ℝ) * x^3 * (z - y)^3 + (120 : ℝ) * x^2 * (y - x)^4 + (240 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (219 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (99 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (42 : ℝ) * x^2 * (z - y)^4 + (96 : ℝ) * x^1 * (y - x)^5 + (240 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (306 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (219 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (117 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (30 : ℝ) * x^1 * (z - y)^5 + (28 : ℝ) * (y - x)^6 + (84 : ℝ) * (y - x)^5 * (z - y)^1 + (135 : ℝ) * (y - x)^4 * (z - y)^2 + (130 : ℝ) * (y - x)^3 * (z - y)^3 + (90 : ℝ) * (y - x)^2 * (z - y)^4 + (39 : ℝ) * (y - x)^1 * (z - y)^5 + (8 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*x^6 - 9*x^5*y - 9*x^5*z + 15*x^4*y^2 - 18*x^4*y*z + 15*x^4*z^2 - 9*x^3*y^2*z - 9*x^3*y*z^2 + 15*x^2*y^4 - 9*x^2*y^3*z + 48*x^2*y^2*z^2 - 9*x^2*y*z^3 + 15*x^2*z^4 - 9*x*y^5 - 18*x*y^4*z - 9*x*y^3*z^2 - 9*x*y^2*z^3 - 18*x*y*z^4 - 9*x*z^5 + 8*y^6 - 9*y^5*z + 15*y^4*z^2 + 15*y^2*z^4 - 9*y*z^5 + 8*z^6) := by
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
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 8 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 ≥ 9 * (x + y) * (y + z) * (z + x) * (x ^ 3 + y ^ 3 + z ^ 3)) := @solution
#print axioms solution
