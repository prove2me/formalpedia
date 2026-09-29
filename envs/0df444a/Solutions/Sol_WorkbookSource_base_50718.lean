-- Prove2me | solution 1 for WorkbookSource.base_50718
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:27.765878+00:00
-- url     : https://prove2.me/submissions/91f26a4f-72c6-4378-88a8-efcacca52d77

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 2 * x ^ 6 + 2 * y ^ 6 + 2 * z ^ 6 + x ^ 3 * y ^ 3 + x ^ 3 * z ^ 3 + y ^ 3 * z ^ 3 ≥ 3 * x ^ 4 * y ^ 2 + 3 * y ^ 4 * z ^ 2 + 3 * z ^ 4 * x ^ 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^6 - 3*x^4*y^2 + x^3*y^3 + x^3*z^3 - 3*x^2*z^4 + 2*y^6 - 3*y^4*z^2 + y^3*z^3 + 2*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (15 : ℝ) * x^4 * (y - x)^2 + (15 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (15 : ℝ) * x^4 * (z - y)^2 + (30 : ℝ) * x^3 * (y - x)^3 + (57 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (87 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (30 : ℝ) * x^3 * (z - y)^3 + (27 : ℝ) * x^2 * (y - x)^4 + (78 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (162 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (111 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (27 : ℝ) * x^2 * (z - y)^4 + (12 : ℝ) * x^1 * (y - x)^5 + (45 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (120 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (123 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (60 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (12 : ℝ) * x^1 * (z - y)^5 + (2 : ℝ) * (y - x)^6 + (9 : ℝ) * (y - x)^5 * (z - y)^1 + (30 : ℝ) * (y - x)^4 * (z - y)^2 + (41 : ℝ) * (y - x)^3 * (z - y)^3 + (30 : ℝ) * (y - x)^2 * (z - y)^4 + (12 : ℝ) * (y - x)^1 * (z - y)^5 + (2 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (2*x^6 - 3*x^4*y^2 + x^3*y^3 + x^3*z^3 - 3*x^2*z^4 + 2*y^6 - 3*y^4*z^2 + y^3*z^3 + 2*z^6) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (15 : ℝ) * x^4 * (z - x)^2 + (15 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (15 : ℝ) * x^4 * (y - z)^2 + (30 : ℝ) * x^3 * (z - x)^3 + (33 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (63 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (30 : ℝ) * x^3 * (y - z)^3 + (27 : ℝ) * x^2 * (z - x)^4 + (30 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (90 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (87 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (27 : ℝ) * x^2 * (y - z)^4 + (12 : ℝ) * x^1 * (z - x)^5 + (15 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (60 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (87 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (54 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (12 : ℝ) * x^1 * (y - z)^5 + (2 : ℝ) * (z - x)^6 + (3 : ℝ) * (z - x)^5 * (y - z)^1 + (15 : ℝ) * (z - x)^4 * (y - z)^2 + (29 : ℝ) * (z - x)^3 * (y - z)^3 + (27 : ℝ) * (z - x)^2 * (y - z)^4 + (12 : ℝ) * (z - x)^1 * (y - z)^5 + (2 : ℝ) * (y - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^6 - 3*x^4*y^2 + x^3*y^3 + x^3*z^3 - 3*x^2*z^4 + 2*y^6 - 3*y^4*z^2 + y^3*z^3 + 2*z^6) := by
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
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 2 * x ^ 6 + 2 * y ^ 6 + 2 * z ^ 6 + x ^ 3 * y ^ 3 + x ^ 3 * z ^ 3 + y ^ 3 * z ^ 3 ≥ 3 * x ^ 4 * y ^ 2 + 3 * y ^ 4 * z ^ 2 + 3 * z ^ 4 * x ^ 2) := @solution
#print axioms solution
