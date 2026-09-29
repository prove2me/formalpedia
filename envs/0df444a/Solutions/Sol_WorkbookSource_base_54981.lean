-- Prove2me | solution 1 for WorkbookSource.base_54981
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:25:02.121319+00:00
-- url     : https://prove2.me/submissions/626b7bb7-f0cc-4dbc-a9e2-747525fef577

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) ≥ 1 / 6 + 3 / 2 * ((x + y) * (z + x) * (y + z) / ((x + y + z) * (x * y + x * z + y * z)))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^5*y + 4*x^5*z + 22*x^4*y*z - 8*x^3*y^3 - 5*x^3*y^2*z - 5*x^3*y*z^2 - 8*x^3*z^3 - 5*x^2*y^3*z - 36*x^2*y^2*z^2 - 5*x^2*y*z^3 + 4*x*y^5 + 22*x*y^4*z - 5*x*y^3*z^2 - 5*x*y^2*z^3 + 22*x*y*z^4 + 4*x*z^5 + 4*y^5*z - 8*y^3*z^3 + 4*y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (88 : ℝ) * x^4 * (y - x)^2 + (88 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (88 : ℝ) * x^4 * (z - y)^2 + (210 : ℝ) * x^3 * (y - x)^3 + (315 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (389 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (142 : ℝ) * x^3 * (z - y)^3 + (164 : ℝ) * x^2 * (y - x)^4 + (328 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (501 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (337 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (62 : ℝ) * x^2 * (z - y)^4 + (42 : ℝ) * x^1 * (y - x)^5 + (105 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (216 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (219 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (82 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (8 : ℝ) * x^1 * (z - y)^5 + (16 : ℝ) * (y - x)^4 * (z - y)^2 + (32 : ℝ) * (y - x)^3 * (z - y)^3 + (20 : ℝ) * (y - x)^2 * (z - y)^4 + (4 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^5*y + 4*x^5*z + 22*x^4*y*z - 8*x^3*y^3 - 5*x^3*y^2*z - 5*x^3*y*z^2 - 8*x^3*z^3 - 5*x^2*y^3*z - 36*x^2*y^2*z^2 - 5*x^2*y*z^3 + 4*x*y^5 + 22*x*y^4*z - 5*x*y^3*z^2 - 5*x*y^2*z^3 + 22*x*y*z^4 + 4*x*z^5 + 4*y^5*z - 8*y^3*z^3 + 4*y*z^5) := by
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
  have hn : 0 ≤ (4*x^5*y + 4*x^5*z + 22*x^4*y*z - 8*x^3*y^3 - 5*x^3*y^2*z - 5*x^3*y*z^2 - 8*x^3*z^3 - 5*x^2*y^3*z - 36*x^2*y^2*z^2 - 5*x^2*y*z^3 + 4*x*y^5 + 22*x*y^4*z - 5*x*y^3*z^2 - 5*x*y^2*z^3 + 22*x*y*z^4 + 4*x*z^5 + 4*y^5*z - 8*y^3*z^3 + 4*y*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) ≥ 1 / 6 + 3 / 2 * ((x + y) * (z + x) * (y + z) / ((x + y + z) * (x * y + x * z + y * z)))) := @solution
#print axioms solution
