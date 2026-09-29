-- Prove2me | solution 1 for WorkbookSource.base_12221
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:42:12.011417+00:00
-- url     : https://prove2.me/submissions/33f1726a-a6b9-42d0-ae06-b2ed628c0166

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + x * z + y * z) + 9 * x * y * z / ((x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2))) ≥ 4  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^5 - x^4*y - x^4*z + 2*x^3*y^2 - 12*x^3*y*z + 2*x^3*z^2 + 2*x^2*y^3 + 7*x^2*y^2*z + 7*x^2*y*z^2 + 2*x^2*z^3 - x*y^4 - 12*x*y^3*z + 7*x*y^2*z^2 - 12*x*y*z^3 - x*z^4 + 3*y^5 - y^4*z + 2*y^3*z^2 + 2*y^2*z^3 - y*z^4 + 3*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * x^3 * (y - x)^2 + (12 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (12 : ℝ) * x^3 * (z - y)^2 + (22 : ℝ) * x^2 * (y - x)^3 + (33 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (39 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (14 : ℝ) * x^2 * (z - y)^3 + (21 : ℝ) * x^1 * (y - x)^4 + (42 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (61 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (40 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (13 : ℝ) * x^1 * (z - y)^4 + (8 : ℝ) * (y - x)^5 + (20 : ℝ) * (y - x)^4 * (z - y)^1 + (32 : ℝ) * (y - x)^3 * (z - y)^2 + (28 : ℝ) * (y - x)^2 * (z - y)^3 + (14 : ℝ) * (y - x)^1 * (z - y)^4 + (3 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^5 - x^4*y - x^4*z + 2*x^3*y^2 - 12*x^3*y*z + 2*x^3*z^2 + 2*x^2*y^3 + 7*x^2*y^2*z + 7*x^2*y*z^2 + 2*x^2*z^3 - x*y^4 - 12*x*y^3*z + 7*x*y^2*z^2 - 12*x*y*z^3 - x*z^4 + 3*y^5 - y^4*z + 2*y^3*z^2 + 2*y^2*z^3 - y*z^4 + 3*z^5) := by
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
  have hn : 0 ≤ (3*x^5 - x^4*y - x^4*z + 2*x^3*y^2 - 12*x^3*y*z + 2*x^3*z^2 + 2*x^2*y^3 + 7*x^2*y^2*z + 7*x^2*y*z^2 + 2*x^2*z^3 - x*y^4 - 12*x*y^3*z + 7*x*y^2*z^2 - 12*x*y*z^3 - x*z^4 + 3*y^5 - y^4*z + 2*y^3*z^2 + 2*y^2*z^3 - y*z^4 + 3*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + x * z + y * z) + 9 * x * y * z / ((x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2))) ≥ 4) := @solution
#print axioms solution
