-- Prove2me | solution 1 for WorkbookSource.base_11082
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:37:14.402642+00:00
-- url     : https://prove2.me/submissions/2abef91c-70ef-498e-bba5-e501e414cedf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y ^ 2 + y * z + z ^ 2) + y / (z ^ 2 + z * x + x ^ 2) + z / (x ^ 2 + x * y + y ^ 2)) ≥ 3 / (x + y + z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6 + 2*x^5*y + 2*x^5*z - x^4*y^2 - x^4*z^2 - x^3*y^3 - x^3*y^2*z - x^3*y*z^2 - x^3*z^3 - x^2*y^4 - x^2*y^3*z - x^2*y*z^3 - x^2*z^4 + 2*x*y^5 - x*y^3*z^2 - x*y^2*z^3 + 2*x*z^5 + y^6 + 2*y^5*z - y^4*z^2 - y^3*z^3 - y^2*z^4 + 2*y*z^5 + z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * x^4 * (y - x)^2 + (27 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (27 : ℝ) * x^4 * (z - y)^2 + (60 : ℝ) * x^3 * (y - x)^3 + (90 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (126 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (48 : ℝ) * x^3 * (z - y)^3 + (51 : ℝ) * x^2 * (y - x)^4 + (102 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (189 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (138 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (33 : ℝ) * x^2 * (z - y)^4 + (20 : ℝ) * x^1 * (y - x)^5 + (50 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (116 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (124 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (58 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (10 : ℝ) * x^1 * (z - y)^5 + (3 : ℝ) * (y - x)^6 + (9 : ℝ) * (y - x)^5 * (z - y)^1 + (25 : ℝ) * (y - x)^4 * (z - y)^2 + (35 : ℝ) * (y - x)^3 * (z - y)^3 + (24 : ℝ) * (y - x)^2 * (z - y)^4 + (8 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6 + 2*x^5*y + 2*x^5*z - x^4*y^2 - x^4*z^2 - x^3*y^3 - x^3*y^2*z - x^3*y*z^2 - x^3*z^3 - x^2*y^4 - x^2*y^3*z - x^2*y*z^3 - x^2*z^4 + 2*x*y^5 - x*y^3*z^2 - x*y^2*z^3 + 2*x*z^5 + y^6 + 2*y^5*z - y^4*z^2 - y^3*z^3 - y^2*z^4 + 2*y*z^5 + z^6) := by
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
  have hn : 0 ≤ (x^6 + 2*x^5*y + 2*x^5*z - x^4*y^2 - x^4*z^2 - x^3*y^3 - x^3*y^2*z - x^3*y*z^2 - x^3*z^3 - x^2*y^4 - x^2*y^3*z - x^2*y*z^3 - x^2*z^4 + 2*x*y^5 - x*y^3*z^2 - x*y^2*z^3 + 2*x*z^5 + y^6 + 2*y^5*z - y^4*z^2 - y^3*z^3 - y^2*z^4 + 2*y*z^5 + z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / (y ^ 2 + y * z + z ^ 2) + y / (z ^ 2 + z * x + x ^ 2) + z / (x ^ 2 + x * y + y ^ 2)) ≥ 3 / (x + y + z)) := @solution
#print axioms solution
