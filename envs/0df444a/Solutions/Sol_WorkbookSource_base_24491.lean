-- Prove2me | solution 1 for WorkbookSource.base_24491
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:12.503875+00:00
-- url     : https://prove2.me/submissions/ae7ce63f-1e2f-4f95-a53d-ede8c93e037c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 / (2 * (x * y + y * z + z * x)) ≥ (x + y) / (x + y + 2 * z) + (y + z) / (y + z + 2 * x) + (z + x) / (z + x + 2 * y)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^5 + 3*x^4*y + 3*x^4*z + x^3*y^2 - 4*x^3*y*z + x^3*z^2 + x^2*y^3 - 6*x^2*y^2*z - 6*x^2*y*z^2 + x^2*z^3 + 3*x*y^4 - 4*x*y^3*z - 6*x*y^2*z^2 - 4*x*y*z^3 + 3*x*z^4 + 2*y^5 + 3*y^4*z + y^3*z^2 + y^2*z^3 + 3*y*z^4 + 2*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * x^3 * (y - x)^2 + (40 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (40 : ℝ) * x^3 * (z - y)^2 + (78 : ℝ) * x^2 * (y - x)^3 + (117 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (123 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (42 : ℝ) * x^2 * (z - y)^3 + (52 : ℝ) * x^1 * (y - x)^4 + (104 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (126 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (74 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (16 : ℝ) * x^1 * (z - y)^4 + (12 : ℝ) * (y - x)^5 + (30 : ℝ) * (y - x)^4 * (z - y)^1 + (42 : ℝ) * (y - x)^3 * (z - y)^2 + (33 : ℝ) * (y - x)^2 * (z - y)^3 + (13 : ℝ) * (y - x)^1 * (z - y)^4 + (2 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^5 + 3*x^4*y + 3*x^4*z + x^3*y^2 - 4*x^3*y*z + x^3*z^2 + x^2*y^3 - 6*x^2*y^2*z - 6*x^2*y*z^2 + x^2*z^3 + 3*x*y^4 - 4*x*y^3*z - 6*x*y^2*z^2 - 4*x*y*z^3 + 3*x*z^4 + 2*y^5 + 3*y^4*z + y^3*z^2 + y^2*z^3 + 3*y*z^4 + 2*z^5) := by
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
  have hn : 0 ≤ (2*x^5 + 3*x^4*y + 3*x^4*z + x^3*y^2 - 4*x^3*y*z + x^3*z^2 + x^2*y^3 - 6*x^2*y^2*z - 6*x^2*y*z^2 + x^2*z^3 + 3*x*y^4 - 4*x*y^3*z - 6*x*y^2*z^2 - 4*x*y*z^3 + 3*x*z^4 + 2*y^5 + 3*y^4*z + y^3*z^2 + y^2*z^3 + 3*y*z^4 + 2*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x + y + z) ^ 2 / (2 * (x * y + y * z + z * x)) ≥ (x + y) / (x + y + 2 * z) + (y + z) / (y + z + 2 * x) + (z + x) / (z + x + 2 * y)) := @solution
#print axioms solution
