-- Prove2me | solution 1 for WorkbookSource.base_17952
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:13:35.004615+00:00
-- url     : https://prove2.me/submissions/04df3e4f-630b-4822-877d-f2be0ae154fc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 + x) * (1 + y) * (1 + z) ≥ (1 + 2 * x * y / (x + y)) * (1 + 2 * y * z / (y + z)) * (1 + 2 * z * x / (z + x))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^3*y^2*z + x^3*y^2 + x^3*y*z^2 + 2*x^3*y*z + x^3*y + x^3*z^2 + x^3*z + x^2*y^3*z + x^2*y^3 - 6*x^2*y^2*z^2 - 4*x^2*y^2*z + x^2*y*z^3 - 4*x^2*y*z^2 - 2*x^2*y*z + x^2*z^3 + x*y^3*z^2 + 2*x*y^3*z + x*y^3 + x*y^2*z^3 - 4*x*y^2*z^2 - 2*x*y^2*z + 2*x*y*z^3 - 2*x*y*z^2 + x*z^3 + y^3*z^2 + y^3*z + y^2*z^3 + y*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * x^4 * (y - x)^2 + (2 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (2 : ℝ) * x^4 * (z - y)^2 + (6 : ℝ) * x^3 * (y - x)^3 + (9 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (6 : ℝ) * x^3 * (y - x)^2 + (7 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (6 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (2 : ℝ) * x^3 * (z - y)^3 + (6 : ℝ) * x^3 * (z - y)^2 + (6 : ℝ) * x^2 * (y - x)^4 + (12 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (14 : ℝ) * x^2 * (y - x)^3 + (9 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (21 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (4 : ℝ) * x^2 * (y - x)^2 + (3 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (15 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (4 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (4 : ℝ) * x^2 * (z - y)^3 + (4 : ℝ) * x^2 * (z - y)^2 + (2 : ℝ) * x^1 * (y - x)^5 + (5 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (10 : ℝ) * x^1 * (y - x)^4 + (4 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (20 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (6 : ℝ) * x^1 * (y - x)^3 + (1 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (14 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (9 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (4 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (7 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (2 : ℝ) * x^1 * (z - y)^3 + (2 : ℝ) * (y - x)^5 + (5 : ℝ) * (y - x)^4 * (z - y)^1 + (2 : ℝ) * (y - x)^4 + (4 : ℝ) * (y - x)^3 * (z - y)^2 + (4 : ℝ) * (y - x)^3 * (z - y)^1 + (1 : ℝ) * (y - x)^2 * (z - y)^3 + (3 : ℝ) * (y - x)^2 * (z - y)^2 + (1 : ℝ) * (y - x)^1 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^3*y^2*z + x^3*y^2 + x^3*y*z^2 + 2*x^3*y*z + x^3*y + x^3*z^2 + x^3*z + x^2*y^3*z + x^2*y^3 - 6*x^2*y^2*z^2 - 4*x^2*y^2*z + x^2*y*z^3 - 4*x^2*y*z^2 - 2*x^2*y*z + x^2*z^3 + x*y^3*z^2 + 2*x*y^3*z + x*y^3 + x*y^2*z^3 - 4*x*y^2*z^2 - 2*x*y^2*z + 2*x*y*z^3 - 2*x*y*z^2 + x*z^3 + y^3*z^2 + y^3*z + y^2*z^3 + y*z^3) := by
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
  have hn : 0 ≤ (x^3*y^2*z + x^3*y^2 + x^3*y*z^2 + 2*x^3*y*z + x^3*y + x^3*z^2 + x^3*z + x^2*y^3*z + x^2*y^3 - 6*x^2*y^2*z^2 - 4*x^2*y^2*z + x^2*y*z^3 - 4*x^2*y*z^2 - 2*x^2*y*z + x^2*z^3 + x*y^3*z^2 + 2*x*y^3*z + x*y^3 + x*y^2*z^3 - 4*x*y^2*z^2 - 2*x*y^2*z + 2*x*y*z^3 - 2*x*y*z^2 + x*z^3 + y^3*z^2 + y^3*z + y^2*z^3 + y*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 + x) * (1 + y) * (1 + z) ≥ (1 + 2 * x * y / (x + y)) * (1 + 2 * y * z / (y + z)) * (1 + 2 * z * x / (z + x))) := @solution
#print axioms solution
