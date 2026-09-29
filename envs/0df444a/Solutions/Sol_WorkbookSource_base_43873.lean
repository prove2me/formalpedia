-- Prove2me | solution 1 for WorkbookSource.base_43873
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:15:12.107675+00:00
-- url     : https://prove2.me/submissions/0a743b90-fa56-421c-9972-29fe3adda820

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + x ^ 3 * z ^ 3) - (x ^ 2 + y ^ 2 + z ^ 2) * (x * y + x * z + y * z) * x * y * z ≥ 0  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y^3 - x^4*y^2*z - x^4*y*z^2 + x^4*z^3 + x^3*y^4 + x^3*y^3*z - x^3*y^2*z^2 + x^3*y*z^3 + x^3*z^4 - x^2*y^4*z - x^2*y^3*z^2 - x^2*y^2*z^3 - x^2*y*z^4 - x*y^4*z^2 + x*y^3*z^3 - x*y^2*z^4 + y^4*z^3 + y^3*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * x^5 * (y - x)^2 + (5 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (5 : ℝ) * x^5 * (z - y)^2 + (22 : ℝ) * x^4 * (y - x)^3 + (33 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (17 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (3 : ℝ) * x^4 * (z - y)^3 + (38 : ℝ) * x^3 * (y - x)^4 + (76 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (44 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (6 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (32 : ℝ) * x^2 * (y - x)^5 + (80 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (64 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (16 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (13 : ℝ) * x^1 * (y - x)^6 + (39 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (41 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (17 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (2 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (2 : ℝ) * (y - x)^7 + (7 : ℝ) * (y - x)^6 * (z - y)^1 + (9 : ℝ) * (y - x)^5 * (z - y)^2 + (5 : ℝ) * (y - x)^4 * (z - y)^3 + (1 : ℝ) * (y - x)^3 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y^3 - x^4*y^2*z - x^4*y*z^2 + x^4*z^3 + x^3*y^4 + x^3*y^3*z - x^3*y^2*z^2 + x^3*y*z^3 + x^3*z^4 - x^2*y^4*z - x^2*y^3*z^2 - x^2*y^2*z^3 - x^2*y*z^4 - x*y^4*z^2 + x*y^3*z^3 - x*y^2*z^4 + y^4*z^3 + y^3*z^4) := by
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
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), (x + y + z) * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + x ^ 3 * z ^ 3) - (x ^ 2 + y ^ 2 + z ^ 2) * (x * y + x * z + y * z) * x * y * z ≥ 0) := @solution
#print axioms solution
