-- Prove2me | solution 1 for WorkbookSource.base_5378
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:37.776868+00:00
-- url     : https://prove2.me/submissions/e60287be-157e-4508-9bdc-03f36a2e4587

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + z * x) + 1 / (z ^ 2 + x * y)) ≤ (1 / 2) * (1 / (x * y) + 1 / (y * z) + 1 / (x * z))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y*z + x^4*y^3 - x^4*y^2*z - x^4*y*z^2 + x^4*z^3 + x^3*y^4 - x^3*y^3*z - x^3*y*z^3 + x^3*z^4 - x^2*y^4*z - x^2*y*z^4 + x*y^5*z - x*y^4*z^2 - x*y^3*z^3 - x*y^2*z^4 + x*y*z^5 + y^4*z^3 + y^3*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^5 * (y - x)^2 + (8 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^5 * (z - y)^2 + (30 : ℝ) * x^4 * (y - x)^3 + (45 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (35 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (10 : ℝ) * x^4 * (z - y)^3 + (45 : ℝ) * x^3 * (y - x)^4 + (90 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (75 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (30 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (5 : ℝ) * x^3 * (z - y)^4 + (34 : ℝ) * x^2 * (y - x)^5 + (85 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (84 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (41 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (10 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (1 : ℝ) * x^2 * (z - y)^5 + (13 : ℝ) * x^1 * (y - x)^6 + (39 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (45 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (25 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (7 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (1 : ℝ) * x^1 * (y - x)^1 * (z - y)^5 + (2 : ℝ) * (y - x)^7 + (7 : ℝ) * (y - x)^6 * (z - y)^1 + (9 : ℝ) * (y - x)^5 * (z - y)^2 + (5 : ℝ) * (y - x)^4 * (z - y)^3 + (1 : ℝ) * (y - x)^3 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y*z + x^4*y^3 - x^4*y^2*z - x^4*y*z^2 + x^4*z^3 + x^3*y^4 - x^3*y^3*z - x^3*y*z^3 + x^3*z^4 - x^2*y^4*z - x^2*y*z^4 + x*y^5*z - x*y^4*z^2 - x*y^3*z^3 - x*y^2*z^4 + x*y*z^5 + y^4*z^3 + y^3*z^4) := by
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
  have hn : 0 ≤ (x^5*y*z + x^4*y^3 - x^4*y^2*z - x^4*y*z^2 + x^4*z^3 + x^3*y^4 - x^3*y^3*z - x^3*y*z^3 + x^3*z^4 - x^2*y^4*z - x^2*y*z^4 + x*y^5*z - x*y^4*z^2 - x*y^3*z^3 - x*y^2*z^4 + x*y*z^5 + y^4*z^3 + y^3*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + z * x) + 1 / (z ^ 2 + x * y)) ≤ (1 / 2) * (1 / (x * y) + 1 / (y * z) + 1 / (x * z))) := @solution
#print axioms solution
