-- Prove2me | solution 1 for WorkbookSource.base_11617
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:39:36.342416+00:00
-- url     : https://prove2.me/submissions/9123a8e7-ca5a-4008-ba48-e24662ad07d3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x ^ 3 / (x + y) + y ^ 3 / (y + z) + z ^ 3 / (z + x)) ≥ (x ^ 2 + y ^ 2 + z ^ 2) / 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y + x^4*z - x^3*y^2 + x^3*z^2 + x^2*y^3 - 2*x^2*y^2*z - 2*x^2*y*z^2 - x^2*z^3 + x*y^4 - 2*x*y^2*z^2 + x*z^4 + y^4*z - y^3*z^2 + y^2*z^3 + y*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^3 * (y - x)^2 + (8 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (8 : ℝ) * x^3 * (z - y)^2 + (16 : ℝ) * x^2 * (y - x)^3 + (27 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (27 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (8 : ℝ) * x^2 * (z - y)^3 + (10 : ℝ) * x^1 * (y - x)^4 + (24 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (28 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (14 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (2 : ℝ) * x^1 * (z - y)^4 + (2 : ℝ) * (y - x)^5 + (6 : ℝ) * (y - x)^4 * (z - y)^1 + (8 : ℝ) * (y - x)^3 * (z - y)^2 + (5 : ℝ) * (y - x)^2 * (z - y)^3 + (1 : ℝ) * (y - x)^1 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (x^4*y + x^4*z - x^3*y^2 + x^3*z^2 + x^2*y^3 - 2*x^2*y^2*z - 2*x^2*y*z^2 - x^2*z^3 + x*y^4 - 2*x*y^2*z^2 + x*z^4 + y^4*z - y^3*z^2 + y^2*z^3 + y*z^4) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * x^3 * (z - x)^2 + (8 : ℝ) * x^3 * (z - x)^1 * (y - z)^1 + (8 : ℝ) * x^3 * (y - z)^2 + (16 : ℝ) * x^2 * (z - x)^3 + (21 : ℝ) * x^2 * (z - x)^2 * (y - z)^1 + (21 : ℝ) * x^2 * (z - x)^1 * (y - z)^2 + (8 : ℝ) * x^2 * (y - z)^3 + (10 : ℝ) * x^1 * (z - x)^4 + (16 : ℝ) * x^1 * (z - x)^3 * (y - z)^1 + (16 : ℝ) * x^1 * (z - x)^2 * (y - z)^2 + (10 : ℝ) * x^1 * (z - x)^1 * (y - z)^3 + (2 : ℝ) * x^1 * (y - z)^4 + (2 : ℝ) * (z - x)^5 + (4 : ℝ) * (z - x)^4 * (y - z)^1 + (4 : ℝ) * (z - x)^3 * (y - z)^2 + (3 : ℝ) * (z - x)^2 * (y - z)^3 + (1 : ℝ) * (z - x)^1 * (y - z)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y + x^4*z - x^3*y^2 + x^3*z^2 + x^2*y^3 - 2*x^2*y^2*z - 2*x^2*y*z^2 - x^2*z^3 + x*y^4 - 2*x*y^2*z^2 + x*z^4 + y^4*z - y^3*z^2 + y^2*z^3 + y*z^4) := by
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
  have hn : 0 ≤ (x^4*y + x^4*z - x^3*y^2 + x^3*z^2 + x^2*y^3 - 2*x^2*y^2*z - 2*x^2*y*z^2 - x^2*z^3 + x*y^4 - 2*x*y^2*z^2 + x*z^4 + y^4*z - y^3*z^2 + y^2*z^3 + y*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x ^ 3 / (x + y) + y ^ 3 / (y + z) + z ^ 3 / (z + x)) ≥ (x ^ 2 + y ^ 2 + z ^ 2) / 2) := @solution
#print axioms solution
