-- Prove2me | solution 1 for WorkbookSource.base_18620
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:37:18.154903+00:00
-- url     : https://prove2.me/submissions/a79d30d7-2546-4753-b188-4c8a8f910f82

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 4 * y + y ^ 4 * z + z ^ 4 * x ≥ (1 / 3) * (x + y + z) ^ 2 * x * y * z  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^4*y - x^3*y*z - 2*x^2*y^2*z - 2*x^2*y*z^2 - x*y^3*z - 2*x*y^2*z^2 - x*y*z^3 + 3*x*z^4 + 3*y^4*z) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * x^3 * (y - x)^2 + (11 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (11 : ℝ) * x^3 * (z - y)^2 + (22 : ℝ) * x^2 * (y - x)^3 + (24 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (24 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (11 : ℝ) * x^2 * (z - y)^3 + (14 : ℝ) * x^1 * (y - x)^4 + (16 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (13 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (11 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (3 : ℝ) * x^1 * (z - y)^4 + (3 : ℝ) * (y - x)^5 + (3 : ℝ) * (y - x)^4 * (z - y)^1 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (3*x^4*y - x^3*y*z - 2*x^2*y^2*z - 2*x^2*y*z^2 - x*y^3*z - 2*x*y^2*z^2 - x*y*z^3 + 3*x*z^4 + 3*y^4*z) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * x^3 * (z - x)^2 + (11 : ℝ) * x^3 * (z - x)^1 * (y - z)^1 + (11 : ℝ) * x^3 * (y - z)^2 + (22 : ℝ) * x^2 * (z - x)^3 + (42 : ℝ) * x^2 * (z - x)^2 * (y - z)^1 + (42 : ℝ) * x^2 * (z - x)^1 * (y - z)^2 + (11 : ℝ) * x^2 * (y - z)^3 + (14 : ℝ) * x^1 * (z - x)^4 + (40 : ℝ) * x^1 * (z - x)^3 * (y - z)^1 + (49 : ℝ) * x^1 * (z - x)^2 * (y - z)^2 + (23 : ℝ) * x^1 * (z - x)^1 * (y - z)^3 + (3 : ℝ) * x^1 * (y - z)^4 + (3 : ℝ) * (z - x)^5 + (12 : ℝ) * (z - x)^4 * (y - z)^1 + (18 : ℝ) * (z - x)^3 * (y - z)^2 + (12 : ℝ) * (z - x)^2 * (y - z)^3 + (3 : ℝ) * (z - x)^1 * (y - z)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^4*y - x^3*y*z - 2*x^2*y^2*z - 2*x^2*y*z^2 - x*y^3*z - 2*x*y^2*z^2 - x*y*z^3 + 3*x*z^4 + 3*y^4*z) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux1 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (3*x^4*y - x^3*y*z - 2*x^2*y^2*z - 2*x^2*y*z^2 - x*y^3*z - 2*x*y^2*z^2 - x*y*z^3 + 3*x*z^4 + 3*y^4*z) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x ^ 4 * y + y ^ 4 * z + z ^ 4 * x ≥ (1 / 3) * (x + y + z) ^ 2 * x * y * z) := @solution
#print axioms solution
