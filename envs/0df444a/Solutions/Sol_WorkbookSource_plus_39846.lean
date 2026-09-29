-- Prove2me | solution 1 for WorkbookSource.plus_39846
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:04:03.096198+00:00
-- url     : https://prove2.me/submissions/a353b6f5-6c58-4b1d-b415-105c4e6cf764

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ (x + y + z) ^ 2 / (x ^ 3 + y ^ 3 + z ^ 3 + 3 * x * y * z)   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5 + 2*x^4*y + 2*x^4*z - 2*x^3*y^2 - 2*x^3*z^2 - 2*x^2*y^3 - x^2*y^2*z - x^2*y*z^2 - 2*x^2*z^3 + 2*x*y^4 - x*y^2*z^2 + 2*x*z^4 + y^5 + 2*y^4*z - 2*y^3*z^2 - 2*y^2*z^3 + 2*y*z^4 + z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * x^3 * (y - x)^2 + (16 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (16 : ℝ) * x^3 * (z - y)^2 + (26 : ℝ) * x^2 * (y - x)^3 + (39 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (57 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (22 : ℝ) * x^2 * (z - y)^3 + (13 : ℝ) * x^1 * (y - x)^4 + (26 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (53 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (40 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (9 : ℝ) * x^1 * (z - y)^4 + (2 : ℝ) * (y - x)^5 + (5 : ℝ) * (y - x)^4 * (z - y)^1 + (14 : ℝ) * (y - x)^3 * (z - y)^2 + (16 : ℝ) * (y - x)^2 * (z - y)^3 + (7 : ℝ) * (y - x)^1 * (z - y)^4 + (1 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5 + 2*x^4*y + 2*x^4*z - 2*x^3*y^2 - 2*x^3*z^2 - 2*x^2*y^3 - x^2*y^2*z - x^2*y*z^2 - 2*x^2*z^3 + 2*x*y^4 - x*y^2*z^2 + 2*x*z^4 + y^5 + 2*y^4*z - 2*y^3*z^2 - 2*y^2*z^3 + 2*y*z^4 + z^5) := by
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
  have hn : 0 ≤ (x^5 + 2*x^4*y + 2*x^4*z - 2*x^3*y^2 - 2*x^3*z^2 - 2*x^2*y^3 - x^2*y^2*z - x^2*y*z^2 - 2*x^2*z^3 + 2*x*y^4 - x*y^2*z^2 + 2*x*z^4 + y^5 + 2*y^4*z - 2*y^3*z^2 - 2*y^2*z^3 + 2*y*z^4 + z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ (x + y + z) ^ 2 / (x ^ 3 + y ^ 3 + z ^ 3 + 3 * x * y * z)) := @solution
#print axioms solution
