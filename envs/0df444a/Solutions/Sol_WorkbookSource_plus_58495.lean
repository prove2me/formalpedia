-- Prove2me | solution 1 for WorkbookSource.plus_58495
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:40:40.419307+00:00
-- url     : https://prove2.me/submissions/f6c5f797-5f70-49e0-9d16-41c1158b1a73

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 5 * (x ^ 6 + y ^ 6 + z ^ 6) + 13 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3) ≥ 27 * x ^ 2 * y ^ 2 * z ^ 2 + 9 * x * y * z * (x ^ 3 + y ^ 3 + z ^ 3)   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (5*x^6 - 9*x^4*y*z + 13*x^3*y^3 + 13*x^3*z^3 - 27*x^2*y^2*z^2 - 9*x*y^4*z - 9*x*y*z^4 + 5*y^6 + 13*y^3*z^3 + 5*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * x^4 * (y - x)^2 + (72 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (72 : ℝ) * x^4 * (z - y)^2 + (198 : ℝ) * x^3 * (y - x)^3 + (297 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (279 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (90 : ℝ) * x^3 * (z - y)^3 + (228 : ℝ) * x^2 * (y - x)^4 + (456 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (495 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (267 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (66 : ℝ) * x^2 * (z - y)^4 + (120 : ℝ) * x^1 * (y - x)^5 + (300 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (402 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (303 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (141 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (30 : ℝ) * x^1 * (z - y)^5 + (23 : ℝ) * (y - x)^6 + (69 : ℝ) * (y - x)^5 * (z - y)^1 + (114 : ℝ) * (y - x)^4 * (z - y)^2 + (113 : ℝ) * (y - x)^3 * (z - y)^3 + (75 : ℝ) * (y - x)^2 * (z - y)^4 + (30 : ℝ) * (y - x)^1 * (z - y)^5 + (5 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*x^6 - 9*x^4*y*z + 13*x^3*y^3 + 13*x^3*z^3 - 27*x^2*y^2*z^2 - 9*x*y^4*z - 9*x*y*z^4 + 5*y^6 + 13*y^3*z^3 + 5*z^6) := by
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
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), 5 * (x ^ 6 + y ^ 6 + z ^ 6) + 13 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3) ≥ 27 * x ^ 2 * y ^ 2 * z ^ 2 + 9 * x * y * z * (x ^ 3 + y ^ 3 + z ^ 3)) := @solution
#print axioms solution
