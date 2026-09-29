-- Prove2me | solution 1 for WorkbookSource.base_36275
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:14:23.175679+00:00
-- url     : https://prove2.me/submissions/72afd024-9968-409d-a952-c71e70466c70

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 2 / (x ^ 2 + y * z) + (z + x) ^ 2 / (y ^ 2 + z * x) + (x + y) ^ 2 / (z ^ 2 + x * y) ≥ 6 + 5 * (y - z) ^ 2 * (z - x) ^ 2 * (x - y) ^ 2 / ((x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y + x^5*z - 4*x^4*y^2 + 8*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 - 8*x^3*y^2*z - 8*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 - 8*x^2*y^3*z + 24*x^2*y^2*z^2 - 8*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 8*x*y^4*z - 8*x*y^3*z^2 - 8*x*y^2*z^3 + 8*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^4 * (y - x)^2 + (8 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^4 * (z - y)^2 + (16 : ℝ) * x^3 * (y - x)^3 + (24 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (40 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (16 : ℝ) * x^3 * (z - y)^3 + (10 : ℝ) * x^2 * (y - x)^4 + (20 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (54 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (44 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (10 : ℝ) * x^2 * (z - y)^4 + (2 : ℝ) * x^1 * (y - x)^5 + (5 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (26 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (34 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (15 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (2 : ℝ) * x^1 * (z - y)^5 + (1 : ℝ) * (y - x)^2 * (z - y)^4 + (1 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y + x^5*z - 4*x^4*y^2 + 8*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 - 8*x^3*y^2*z - 8*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 - 8*x^2*y^3*z + 24*x^2*y^2*z^2 - 8*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 8*x*y^4*z - 8*x*y^3*z^2 - 8*x*y^2*z^3 + 8*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by
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
  have hn : 0 ≤ (x^5*y + x^5*z - 4*x^4*y^2 + 8*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 - 8*x^3*y^2*z - 8*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 - 8*x^2*y^3*z + 24*x^2*y^2*z^2 - 8*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 8*x*y^4*z - 8*x*y^3*z^2 - 8*x*y^2*z^3 + 8*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y + z) ^ 2 / (x ^ 2 + y * z) + (z + x) ^ 2 / (y ^ 2 + z * x) + (x + y) ^ 2 / (z ^ 2 + x * y) ≥ 6 + 5 * (y - z) ^ 2 * (z - x) ^ 2 * (x - y) ^ 2 / ((x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y))) := @solution
#print axioms solution
