-- Prove2me | solution 1 for WorkbookSource.plus_10270
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:23:50.885659+00:00
-- url     : https://prove2.me/submissions/2c0142fb-8266-4079-ab6c-759a8b7e18ab

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 27 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ (x + y + z) ^ 4 * ((y + z - x) ^ 2 + (z + x - y) ^ 2 + (x + y - z) ^ 2)   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (24*x^6 - 10*x^5*y - 10*x^5*z - 13*x^4*y^2 - 18*x^4*y*z - 13*x^4*z^2 + 42*x^3*y^3 - 4*x^3*y^2*z - 4*x^3*y*z^2 + 42*x^3*z^3 - 13*x^2*y^4 - 4*x^2*y^3*z + 18*x^2*y^2*z^2 - 4*x^2*y*z^3 - 13*x^2*z^4 - 10*x*y^5 - 18*x*y^4*z - 4*x*y^3*z^2 - 4*x*y^2*z^3 - 18*x*y*z^4 - 10*x*z^5 + 24*y^6 - 10*y^5*z - 13*y^4*z^2 + 42*y^3*z^3 - 13*y^2*z^4 - 10*y*z^5 + 24*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (108 : ℝ) * x^4 * (y - x)^2 + (108 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (108 : ℝ) * x^4 * (z - y)^2 + (252 : ℝ) * x^3 * (y - x)^3 + (378 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (486 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (180 : ℝ) * x^3 * (z - y)^3 + (324 : ℝ) * x^2 * (y - x)^4 + (648 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (1026 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (702 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (216 : ℝ) * x^2 * (z - y)^4 + (200 : ℝ) * x^1 * (y - x)^5 + (500 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (956 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (934 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (526 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (124 : ℝ) * x^1 * (z - y)^5 + (44 : ℝ) * (y - x)^6 + (132 : ℝ) * (y - x)^5 * (z - y)^1 + (295 : ℝ) * (y - x)^4 * (z - y)^2 + (370 : ℝ) * (y - x)^3 * (z - y)^3 + (297 : ℝ) * (y - x)^2 * (z - y)^4 + (134 : ℝ) * (y - x)^1 * (z - y)^5 + (24 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (24*x^6 - 10*x^5*y - 10*x^5*z - 13*x^4*y^2 - 18*x^4*y*z - 13*x^4*z^2 + 42*x^3*y^3 - 4*x^3*y^2*z - 4*x^3*y*z^2 + 42*x^3*z^3 - 13*x^2*y^4 - 4*x^2*y^3*z + 18*x^2*y^2*z^2 - 4*x^2*y*z^3 - 13*x^2*z^4 - 10*x*y^5 - 18*x*y^4*z - 4*x*y^3*z^2 - 4*x*y^2*z^3 - 18*x*y*z^4 - 10*x*z^5 + 24*y^6 - 10*y^5*z - 13*y^4*z^2 + 42*y^3*z^3 - 13*y^2*z^4 - 10*y*z^5 + 24*z^6) := by
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
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), 27 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ (x + y + z) ^ 4 * ((y + z - x) ^ 2 + (z + x - y) ^ 2 + (x + y - z) ^ 2)) := @solution
#print axioms solution
