-- Prove2me | solution 1 for WorkbookSource.base_14803
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:57:00.034594+00:00
-- url     : https://prove2.me/submissions/be31ef05-c693-46f1-aae0-0141f9e7e395

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2) ≥ 2 * x * y / (x ^ 2 + y ^ 2) + 2 * y * z / (y ^ 2 + z ^ 2) + 2 * z * x / (z ^ 2 + x ^ 2)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6*y^2 - 2*x^6*y*z + x^6*z^2 + 2*x^4*y^4 - 2*x^4*y^3*z + 4*x^4*y^2*z^2 - 2*x^4*y*z^3 + 2*x^4*z^4 - 2*x^3*y^4*z - 2*x^3*y^3*z^2 - 2*x^3*y^2*z^3 - 2*x^3*y*z^4 + x^2*y^6 + 4*x^2*y^4*z^2 - 2*x^2*y^3*z^3 + 4*x^2*y^2*z^4 + x^2*z^6 - 2*x*y^6*z - 2*x*y^4*z^3 - 2*x*y^3*z^4 - 2*x*y*z^6 + y^6*z^2 + 2*y^4*z^4 + y^2*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^6 * (y - x)^2 + (8 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^6 * (z - y)^2 + (40 : ℝ) * x^5 * (y - x)^3 + (60 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (36 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (8 : ℝ) * x^5 * (z - y)^3 + (84 : ℝ) * x^4 * (y - x)^4 + (168 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (112 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (28 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (4 : ℝ) * x^4 * (z - y)^4 + (96 : ℝ) * x^3 * (y - x)^5 + (240 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (208 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (72 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (8 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (64 : ℝ) * x^2 * (y - x)^6 + (192 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (217 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (114 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (25 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (24 : ℝ) * x^1 * (y - x)^7 + (84 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (120 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (90 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (36 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (6 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (4 : ℝ) * (y - x)^8 + (16 : ℝ) * (y - x)^7 * (z - y)^1 + (28 : ℝ) * (y - x)^6 * (z - y)^2 + (28 : ℝ) * (y - x)^5 * (z - y)^3 + (17 : ℝ) * (y - x)^4 * (z - y)^4 + (6 : ℝ) * (y - x)^3 * (z - y)^5 + (1 : ℝ) * (y - x)^2 * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6*y^2 - 2*x^6*y*z + x^6*z^2 + 2*x^4*y^4 - 2*x^4*y^3*z + 4*x^4*y^2*z^2 - 2*x^4*y*z^3 + 2*x^4*z^4 - 2*x^3*y^4*z - 2*x^3*y^3*z^2 - 2*x^3*y^2*z^3 - 2*x^3*y*z^4 + x^2*y^6 + 4*x^2*y^4*z^2 - 2*x^2*y^3*z^3 + 4*x^2*y^2*z^4 + x^2*z^6 - 2*x*y^6*z - 2*x*y^4*z^3 - 2*x*y^3*z^4 - 2*x*y*z^6 + y^6*z^2 + 2*y^4*z^4 + y^2*z^6) := by
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
  have hn : 0 ≤ (x^6*y^2 - 2*x^6*y*z + x^6*z^2 + 2*x^4*y^4 - 2*x^4*y^3*z + 4*x^4*y^2*z^2 - 2*x^4*y*z^3 + 2*x^4*z^4 - 2*x^3*y^4*z - 2*x^3*y^3*z^2 - 2*x^3*y^2*z^3 - 2*x^3*y*z^4 + x^2*y^6 + 4*x^2*y^4*z^2 - 2*x^2*y^3*z^3 + 4*x^2*y^2*z^4 + x^2*z^6 - 2*x*y^6*z - 2*x*y^4*z^3 - 2*x*y^3*z^4 - 2*x*y*z^6 + y^6*z^2 + 2*y^4*z^4 + y^2*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2) ≥ 2 * x * y / (x ^ 2 + y ^ 2) + 2 * y * z / (y ^ 2 + z ^ 2) + 2 * z * x / (z ^ 2 + x ^ 2)) := @solution
#print axioms solution
