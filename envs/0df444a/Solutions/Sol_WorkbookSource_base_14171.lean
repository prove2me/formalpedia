-- Prove2me | solution 1 for WorkbookSource.base_14171
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:53:13.394638+00:00
-- url     : https://prove2.me/submissions/05d49f58-365c-423f-b4c5-819a61dbeb04

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * x / (y * z + x ^ 2) + 2 * y / (z * x + y ^ 2) + 2 * z / (x * y + z ^ 2)) ≤ 1 / x + 1 / y + 1 / z  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y^2*z + x^5*y*z^2 + x^4*y^4 - x^4*y^3*z - x^4*y^2*z^2 - x^4*y*z^3 + x^4*z^4 - x^3*y^4*z - x^3*y*z^4 + x^2*y^5*z - x^2*y^4*z^2 - x^2*y^2*z^4 + x^2*y*z^5 + x*y^5*z^2 - x*y^4*z^3 - x*y^3*z^4 + x*y^2*z^5 + y^4*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^6 * (y - x)^2 + (8 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^6 * (z - y)^2 + (34 : ℝ) * x^5 * (y - x)^3 + (51 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (45 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (14 : ℝ) * x^5 * (z - y)^3 + (59 : ℝ) * x^4 * (y - x)^4 + (118 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (112 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (53 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (9 : ℝ) * x^4 * (z - y)^4 + (54 : ℝ) * x^3 * (y - x)^5 + (135 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (146 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (84 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (23 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (2 : ℝ) * x^3 * (z - y)^5 + (28 : ℝ) * x^2 * (y - x)^6 + (84 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (103 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (66 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (22 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (3 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (8 : ℝ) * x^1 * (y - x)^7 + (28 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (38 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (25 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (8 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (1 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (1 : ℝ) * (y - x)^8 + (4 : ℝ) * (y - x)^7 * (z - y)^1 + (6 : ℝ) * (y - x)^6 * (z - y)^2 + (4 : ℝ) * (y - x)^5 * (z - y)^3 + (1 : ℝ) * (y - x)^4 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y^2*z + x^5*y*z^2 + x^4*y^4 - x^4*y^3*z - x^4*y^2*z^2 - x^4*y*z^3 + x^4*z^4 - x^3*y^4*z - x^3*y*z^4 + x^2*y^5*z - x^2*y^4*z^2 - x^2*y^2*z^4 + x^2*y*z^5 + x*y^5*z^2 - x*y^4*z^3 - x*y^3*z^4 + x*y^2*z^5 + y^4*z^4) := by
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
  have hn : 0 ≤ (x^5*y^2*z + x^5*y*z^2 + x^4*y^4 - x^4*y^3*z - x^4*y^2*z^2 - x^4*y*z^3 + x^4*z^4 - x^3*y^4*z - x^3*y*z^4 + x^2*y^5*z - x^2*y^4*z^2 - x^2*y^2*z^4 + x^2*y*z^5 + x*y^5*z^2 - x*y^4*z^3 - x*y^3*z^4 + x*y^2*z^5 + y^4*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (2 * x / (y * z + x ^ 2) + 2 * y / (z * x + y ^ 2) + 2 * z / (x * y + z ^ 2)) ≤ 1 / x + 1 / y + 1 / z) := @solution
#print axioms solution
