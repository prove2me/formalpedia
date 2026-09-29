-- Prove2me | solution 1 for WorkbookSource.base_15137
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:00:03.680762+00:00
-- url     : https://prove2.me/submissions/425832a9-164f-41be-b883-3adcb9d3fdd9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x + y + z ≥ 4*x*y*z * (1/((x+y)^2) + 1/((x+z)^2) + 1/((y+z)^2))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y^2 - 2*x^5*y*z + x^5*z^2 + 3*x^4*y^3 + x^4*y^2*z + x^4*y*z^2 + 3*x^4*z^3 + 3*x^3*y^4 + 2*x^3*y^3*z - 10*x^3*y^2*z^2 + 2*x^3*y*z^3 + 3*x^3*z^4 + x^2*y^5 + x^2*y^4*z - 10*x^2*y^3*z^2 - 10*x^2*y^2*z^3 + x^2*y*z^4 + x^2*z^5 - 2*x*y^5*z + x*y^4*z^2 + 2*x*y^3*z^3 + x*y^2*z^4 - 2*x*y*z^5 + y^5*z^2 + 3*y^4*z^3 + 3*y^3*z^4 + y^2*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * x^5 * (y - x)^2 + (32 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (32 : ℝ) * x^5 * (z - y)^2 + (128 : ℝ) * x^4 * (y - x)^3 + (192 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (128 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (32 : ℝ) * x^4 * (z - y)^3 + (200 : ℝ) * x^3 * (y - x)^4 + (400 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (280 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (80 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (8 : ℝ) * x^3 * (z - y)^4 + (152 : ℝ) * x^2 * (y - x)^5 + (380 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (328 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (112 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (12 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (56 : ℝ) * x^1 * (y - x)^6 + (168 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (183 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (86 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (15 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (8 : ℝ) * (y - x)^7 + (28 : ℝ) * (y - x)^6 * (z - y)^1 + (38 : ℝ) * (y - x)^5 * (z - y)^2 + (25 : ℝ) * (y - x)^4 * (z - y)^3 + (8 : ℝ) * (y - x)^3 * (z - y)^4 + (1 : ℝ) * (y - x)^2 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y^2 - 2*x^5*y*z + x^5*z^2 + 3*x^4*y^3 + x^4*y^2*z + x^4*y*z^2 + 3*x^4*z^3 + 3*x^3*y^4 + 2*x^3*y^3*z - 10*x^3*y^2*z^2 + 2*x^3*y*z^3 + 3*x^3*z^4 + x^2*y^5 + x^2*y^4*z - 10*x^2*y^3*z^2 - 10*x^2*y^2*z^3 + x^2*y*z^4 + x^2*z^5 - 2*x*y^5*z + x*y^4*z^2 + 2*x*y^3*z^3 + x*y^2*z^4 - 2*x*y*z^5 + y^5*z^2 + 3*y^4*z^3 + 3*y^3*z^4 + y^2*z^5) := by
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
  have hn : 0 ≤ (x^5*y^2 - 2*x^5*y*z + x^5*z^2 + 3*x^4*y^3 + x^4*y^2*z + x^4*y*z^2 + 3*x^4*z^3 + 3*x^3*y^4 + 2*x^3*y^3*z - 10*x^3*y^2*z^2 + 2*x^3*y*z^3 + 3*x^3*z^4 + x^2*y^5 + x^2*y^4*z - 10*x^2*y^3*z^2 - 10*x^2*y^2*z^3 + x^2*y*z^4 + x^2*z^5 - 2*x*y^5*z + x*y^4*z^2 + 2*x*y^3*z^3 + x*y^2*z^4 - 2*x*y*z^5 + y^5*z^2 + 3*y^4*z^3 + 3*y^3*z^4 + y^2*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x + y + z ≥ 4*x*y*z * (1/((x+y)^2) + 1/((x+z)^2) + 1/((y+z)^2))) := @solution
#print axioms solution
