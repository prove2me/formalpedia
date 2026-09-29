-- Prove2me | solution 1 for WorkbookSource.plus_78115
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:40.03523+00:00
-- url     : https://prove2.me/submissions/17263089-f820-4ec4-b3f3-3efce8484ebf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 5 + y ^ 5 + z ^ 5 - x ^ 3 * z ^ 2 - y ^ 3 * x ^ 2 - z ^ 3 * y ^ 2 ≥ 0   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5 - x^3*z^2 - x^2*y^3 + y^5 - y^2*z^3 + z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^3 * (y - x)^2 + (6 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (6 : ℝ) * x^3 * (z - y)^2 + (9 : ℝ) * x^2 * (y - x)^3 + (12 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (21 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (9 : ℝ) * x^2 * (z - y)^3 + (5 : ℝ) * x^1 * (y - x)^4 + (8 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (21 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (18 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (5 : ℝ) * x^1 * (z - y)^4 + (1 : ℝ) * (y - x)^5 + (2 : ℝ) * (y - x)^4 * (z - y)^1 + (7 : ℝ) * (y - x)^3 * (z - y)^2 + (9 : ℝ) * (y - x)^2 * (z - y)^3 + (5 : ℝ) * (y - x)^1 * (z - y)^4 + (1 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^5 - x^3*z^2 - x^2*y^3 + y^5 - y^2*z^3 + z^5) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * x^3 * (z - x)^2 + (6 : ℝ) * x^3 * (z - x)^1 * (y - z)^1 + (6 : ℝ) * x^3 * (y - z)^2 + (9 : ℝ) * x^2 * (z - x)^3 + (15 : ℝ) * x^2 * (z - x)^2 * (y - z)^1 + (24 : ℝ) * x^2 * (z - x)^1 * (y - z)^2 + (9 : ℝ) * x^2 * (y - z)^3 + (5 : ℝ) * x^1 * (z - x)^4 + (12 : ℝ) * x^1 * (z - x)^3 * (y - z)^1 + (27 : ℝ) * x^1 * (z - x)^2 * (y - z)^2 + (20 : ℝ) * x^1 * (z - x)^1 * (y - z)^3 + (5 : ℝ) * x^1 * (y - z)^4 + (1 : ℝ) * (z - x)^5 + (3 : ℝ) * (z - x)^4 * (y - z)^1 + (9 : ℝ) * (z - x)^3 * (y - z)^2 + (10 : ℝ) * (z - x)^2 * (y - z)^3 + (5 : ℝ) * (z - x)^1 * (y - z)^4 + (1 : ℝ) * (y - z)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5 - x^3*z^2 - x^2*y^3 + y^5 - y^2*z^3 + z^5) := by
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
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x ^ 5 + y ^ 5 + z ^ 5 - x ^ 3 * z ^ 2 - y ^ 3 * x ^ 2 - z ^ 3 * y ^ 2 ≥ 0) := @solution
#print axioms solution
