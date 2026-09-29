-- Prove2me | solution 1 for WorkbookSource.base_25667
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:06:28.331713+00:00
-- url     : https://prove2.me/submissions/7f977797-0ba5-4a98-bb2e-3cc2f15b3ab4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 ≥ (x / (x + y) + (z + x) / (2 * x + z + y)) * (y / (y + z) + (x + y) / (2 * y + x + z)) * (z / (z + x) + (y + z) / (2 * z + y + x))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^5*y + 2*x^5*z + 3*x^4*y^2 + 3*x^4*y*z + 3*x^4*z^2 + x^3*y^3 - 4*x^3*y^2*z - 4*x^3*y*z^2 + x^3*z^3 + 3*x^2*y^4 - 4*x^2*y^3*z - 18*x^2*y^2*z^2 - 4*x^2*y*z^3 + 3*x^2*z^4 + 2*x*y^5 + 3*x*y^4*z - 4*x*y^3*z^2 - 4*x*y^2*z^3 + 3*x*y*z^4 + 2*x*z^5 + 2*y^5*z + 3*y^4*z^2 + y^3*z^3 + 3*y^2*z^4 + 2*y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (56 : ℝ) * x^4 * (y - x)^2 + (56 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (56 : ℝ) * x^4 * (z - y)^2 + (154 : ℝ) * x^3 * (y - x)^3 + (231 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (217 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (70 : ℝ) * x^3 * (z - y)^3 + (155 : ℝ) * x^2 * (y - x)^4 + (310 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (318 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (163 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (29 : ℝ) * x^2 * (z - y)^4 + (68 : ℝ) * x^1 * (y - x)^5 + (170 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (198 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (127 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (39 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (4 : ℝ) * x^1 * (z - y)^5 + (11 : ℝ) * (y - x)^6 + (33 : ℝ) * (y - x)^5 * (z - y)^1 + (44 : ℝ) * (y - x)^4 * (z - y)^2 + (33 : ℝ) * (y - x)^3 * (z - y)^3 + (13 : ℝ) * (y - x)^2 * (z - y)^4 + (2 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^5*y + 2*x^5*z + 3*x^4*y^2 + 3*x^4*y*z + 3*x^4*z^2 + x^3*y^3 - 4*x^3*y^2*z - 4*x^3*y*z^2 + x^3*z^3 + 3*x^2*y^4 - 4*x^2*y^3*z - 18*x^2*y^2*z^2 - 4*x^2*y*z^3 + 3*x^2*z^4 + 2*x*y^5 + 3*x*y^4*z - 4*x*y^3*z^2 - 4*x*y^2*z^3 + 3*x*y*z^4 + 2*x*z^5 + 2*y^5*z + 3*y^4*z^2 + y^3*z^3 + 3*y^2*z^4 + 2*y*z^5) := by
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
  have hn : 0 ≤ (2*x^5*y + 2*x^5*z + 3*x^4*y^2 + 3*x^4*y*z + 3*x^4*z^2 + x^3*y^3 - 4*x^3*y^2*z - 4*x^3*y*z^2 + x^3*z^3 + 3*x^2*y^4 - 4*x^2*y^3*z - 18*x^2*y^2*z^2 - 4*x^2*y*z^3 + 3*x^2*z^4 + 2*x*y^5 + 3*x*y^4*z - 4*x*y^3*z^2 - 4*x*y^2*z^3 + 3*x*y*z^4 + 2*x*z^5 + 2*y^5*z + 3*y^4*z^2 + y^3*z^3 + 3*y^2*z^4 + 2*y*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 1 ≥ (x / (x + y) + (z + x) / (2 * x + z + y)) * (y / (y + z) + (x + y) / (2 * y + x + z)) * (z / (z + x) + (y + z) / (2 * z + y + x))) := @solution
#print axioms solution
