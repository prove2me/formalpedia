-- Prove2me | solution 1 for WorkbookSource.base_25302
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:03:50.847047+00:00
-- url     : https://prove2.me/submissions/63aeeb98-ef4c-4ce2-8c0f-5cc07011e306

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) + 3 * (x * y * z) / (y * z * (y + z) + z * x * (z + x) + x * y * (x + y)) ≤ 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^4*y^2 + 3*x^4*z^2 + 6*x^3*y^3 - x^3*y^2*z - x^3*y*z^2 + 6*x^3*z^3 + 3*x^2*y^4 - x^2*y^3*z - 30*x^2*y^2*z^2 - x^2*y*z^3 + 3*x^2*z^4 - x*y^3*z^2 - x*y^2*z^3 + 3*y^4*z^2 + 6*y^3*z^3 + 3*y^2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * x^4 * (y - x)^2 + (40 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (40 : ℝ) * x^4 * (z - y)^2 + (126 : ℝ) * x^3 * (y - x)^3 + (189 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (131 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (34 : ℝ) * x^3 * (z - y)^3 + (144 : ℝ) * x^2 * (y - x)^4 + (288 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (207 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (63 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (6 : ℝ) * x^2 * (z - y)^4 + (70 : ℝ) * x^1 * (y - x)^5 + (175 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (152 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (53 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (6 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (12 : ℝ) * (y - x)^6 + (36 : ℝ) * (y - x)^5 * (z - y)^1 + (39 : ℝ) * (y - x)^4 * (z - y)^2 + (18 : ℝ) * (y - x)^3 * (z - y)^3 + (3 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^4*y^2 + 3*x^4*z^2 + 6*x^3*y^3 - x^3*y^2*z - x^3*y*z^2 + 6*x^3*z^3 + 3*x^2*y^4 - x^2*y^3*z - 30*x^2*y^2*z^2 - x^2*y*z^3 + 3*x^2*z^4 - x*y^3*z^2 - x*y^2*z^3 + 3*y^4*z^2 + 6*y^3*z^3 + 3*y^2*z^4) := by
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
  have hn : 0 ≤ (3*x^4*y^2 + 3*x^4*z^2 + 6*x^3*y^3 - x^3*y^2*z - x^3*y*z^2 + 6*x^3*z^3 + 3*x^2*y^4 - x^2*y^3*z - 30*x^2*y^2*z^2 - x^2*y*z^3 + 3*x^2*z^4 - x*y^3*z^2 - x*y^2*z^3 + 3*y^4*z^2 + 6*y^3*z^3 + 3*y^2*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) + 3 * (x * y * z) / (y * z * (y + z) + z * x * (z + x) + x * y * (x + y)) ≤ 2) := @solution
#print axioms solution
