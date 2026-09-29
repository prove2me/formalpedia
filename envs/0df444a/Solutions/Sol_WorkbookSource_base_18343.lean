-- Prove2me | solution 1 for WorkbookSource.base_18343
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:34:38.150251+00:00
-- url     : https://prove2.me/submissions/82bc277c-edbd-49b2-be40-587b11715de4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2) ≥ 5 / (2 * (x * y + y * z + z * x))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^5*y + 2*x^5*z - 5*x^4*y^2 + 2*x^4*y*z - 5*x^4*z^2 + 6*x^3*y^3 + 6*x^3*y^2*z + 6*x^3*y*z^2 + 6*x^3*z^3 - 5*x^2*y^4 + 6*x^2*y^3*z - 10*x^2*y^2*z^2 + 6*x^2*y*z^3 - 5*x^2*z^4 + 2*x*y^5 + 2*x*y^4*z + 6*x*y^3*z^2 + 6*x*y^2*z^3 + 2*x*y*z^4 + 2*x*z^5 + 2*y^5*z - 5*y^4*z^2 + 6*y^3*z^3 - 5*y^2*z^4 + 2*y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * x^6 + (128 : ℝ) * x^5 * (y - x)^1 + (64 : ℝ) * x^5 * (z - y)^1 + (216 : ℝ) * x^4 * (y - x)^2 + (216 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (56 : ℝ) * x^4 * (z - y)^2 + (192 : ℝ) * x^3 * (y - x)^3 + (288 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (160 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (32 : ℝ) * x^3 * (z - y)^3 + (92 : ℝ) * x^2 * (y - x)^4 + (184 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (164 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (72 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (12 : ℝ) * x^2 * (z - y)^4 + (20 : ℝ) * x^1 * (y - x)^5 + (50 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (68 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (52 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (22 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (4 : ℝ) * x^1 * (z - y)^5 + (3 : ℝ) * (y - x)^4 * (z - y)^2 + (6 : ℝ) * (y - x)^3 * (z - y)^3 + (5 : ℝ) * (y - x)^2 * (z - y)^4 + (2 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^5*y + 2*x^5*z - 5*x^4*y^2 + 2*x^4*y*z - 5*x^4*z^2 + 6*x^3*y^3 + 6*x^3*y^2*z + 6*x^3*y*z^2 + 6*x^3*z^3 - 5*x^2*y^4 + 6*x^2*y^3*z - 10*x^2*y^2*z^2 + 6*x^2*y*z^3 - 5*x^2*z^4 + 2*x*y^5 + 2*x*y^4*z + 6*x*y^3*z^2 + 6*x*y^2*z^3 + 2*x*y*z^4 + 2*x*z^5 + 2*y^5*z - 5*y^4*z^2 + 6*y^3*z^3 - 5*y^2*z^4 + 2*y*z^5) := by
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
  have hn : 0 ≤ (2*x^5*y + 2*x^5*z - 5*x^4*y^2 + 2*x^4*y*z - 5*x^4*z^2 + 6*x^3*y^3 + 6*x^3*y^2*z + 6*x^3*y*z^2 + 6*x^3*z^3 - 5*x^2*y^4 + 6*x^2*y^3*z - 10*x^2*y^2*z^2 + 6*x^2*y*z^3 - 5*x^2*z^4 + 2*x*y^5 + 2*x*y^4*z + 6*x*y^3*z^2 + 6*x*y^2*z^3 + 2*x*y*z^4 + 2*x*z^5 + 2*y^5*z - 5*y^4*z^2 + 6*y^3*z^3 - 5*y^2*z^4 + 2*y*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2) ≥ 5 / (2 * (x * y + y * z + z * x))) := @solution
#print axioms solution
