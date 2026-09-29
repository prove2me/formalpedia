-- Prove2me | solution 1 for WorkbookSource.base_11443
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:39:34.998746+00:00
-- url     : https://prove2.me/submissions/ca611b81-dcb3-47be-8dea-08e7a1d67f39

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / (x * y + 2 * z ^ 2) + 1 / (y * z + 2 * x ^ 2) + 1 / (z * x + 2 * y ^ 2) ≤ (x * y + y * z + z * x) / (x * y * z * (x + y + z))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^4*y^4 - 2*x^4*y^3*z - 3*x^4*y^2*z^2 - 2*x^4*y*z^3 + 4*x^4*z^4 - 2*x^3*y^4*z + 3*x^3*y^3*z^2 + 3*x^3*y^2*z^3 - 2*x^3*y*z^4 - 3*x^2*y^4*z^2 + 3*x^2*y^3*z^3 - 3*x^2*y^2*z^4 - 2*x*y^4*z^3 - 2*x*y^3*z^4 + 4*y^4*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * x^6 * (y - x)^2 + (9 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (9 : ℝ) * x^6 * (z - y)^2 + (48 : ℝ) * x^5 * (y - x)^3 + (72 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (36 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (6 : ℝ) * x^5 * (z - y)^3 + (106 : ℝ) * x^4 * (y - x)^4 + (212 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (123 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (17 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (1 : ℝ) * x^4 * (z - y)^4 + (124 : ℝ) * x^3 * (y - x)^5 + (310 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (252 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (68 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (2 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (81 : ℝ) * x^2 * (y - x)^6 + (243 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (258 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (111 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (15 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (28 : ℝ) * x^1 * (y - x)^7 + (98 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (126 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (70 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (14 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (4 : ℝ) * (y - x)^8 + (16 : ℝ) * (y - x)^7 * (z - y)^1 + (24 : ℝ) * (y - x)^6 * (z - y)^2 + (16 : ℝ) * (y - x)^5 * (z - y)^3 + (4 : ℝ) * (y - x)^4 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^4*y^4 - 2*x^4*y^3*z - 3*x^4*y^2*z^2 - 2*x^4*y*z^3 + 4*x^4*z^4 - 2*x^3*y^4*z + 3*x^3*y^3*z^2 + 3*x^3*y^2*z^3 - 2*x^3*y*z^4 - 3*x^2*y^4*z^2 + 3*x^2*y^3*z^3 - 3*x^2*y^2*z^4 - 2*x*y^4*z^3 - 2*x*y^3*z^4 + 4*y^4*z^4) := by
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
  have hn : 0 ≤ (4*x^4*y^4 - 2*x^4*y^3*z - 3*x^4*y^2*z^2 - 2*x^4*y*z^3 + 4*x^4*z^4 - 2*x^3*y^4*z + 3*x^3*y^3*z^2 + 3*x^3*y^2*z^3 - 2*x^3*y*z^4 - 3*x^2*y^4*z^2 + 3*x^2*y^3*z^3 - 3*x^2*y^2*z^4 - 2*x*y^4*z^3 - 2*x*y^3*z^4 + 4*y^4*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 1 / (x * y + 2 * z ^ 2) + 1 / (y * z + 2 * x ^ 2) + 1 / (z * x + 2 * y ^ 2) ≤ (x * y + y * z + z * x) / (x * y * z * (x + y + z))) := @solution
#print axioms solution
