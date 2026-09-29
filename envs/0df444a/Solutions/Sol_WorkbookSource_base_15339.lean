-- Prove2me | solution 1 for WorkbookSource.base_15339
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:02.644072+00:00
-- url     : https://prove2.me/submissions/09f78d48-5461-4163-8a85-5c9e5bf25e18

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (3 * x + y) + 1 / (3 * y + z) + 1 / (3 * z + x)) ≥ (1 / (2 * x + y + z) + 1 / (2 * y + z + x) + 1 / (2 * z + x + y))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (6*x^5 + 2*x^4*y + 32*x^4*z + 4*x^3*y^2 - 16*x^3*y*z + 40*x^3*z^2 + 40*x^2*y^3 - 68*x^2*y^2*z - 68*x^2*y*z^2 + 4*x^2*z^3 + 32*x*y^4 - 16*x*y^3*z - 68*x*y^2*z^2 - 16*x*y*z^3 + 2*x*z^4 + 6*y^5 + 2*y^4*z + 4*y^3*z^2 + 40*y^2*z^3 + 32*y*z^4 + 6*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (256 : ℝ) * x^3 * (y - x)^2 + (256 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (256 : ℝ) * x^3 * (z - y)^2 + (544 : ℝ) * x^2 * (y - x)^3 + (960 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (864 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (224 : ℝ) * x^2 * (z - y)^3 + (384 : ℝ) * x^1 * (y - x)^4 + (960 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (1024 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (448 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (64 : ℝ) * x^1 * (z - y)^4 + (90 : ℝ) * (y - x)^5 + (288 : ℝ) * (y - x)^4 * (z - y)^1 + (376 : ℝ) * (y - x)^3 * (z - y)^2 + (228 : ℝ) * (y - x)^2 * (z - y)^3 + (62 : ℝ) * (y - x)^1 * (z - y)^4 + (6 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (6*x^5 + 2*x^4*y + 32*x^4*z + 4*x^3*y^2 - 16*x^3*y*z + 40*x^3*z^2 + 40*x^2*y^3 - 68*x^2*y^2*z - 68*x^2*y*z^2 + 4*x^2*z^3 + 32*x*y^4 - 16*x*y^3*z - 68*x*y^2*z^2 - 16*x*y*z^3 + 2*x*z^4 + 6*y^5 + 2*y^4*z + 4*y^3*z^2 + 40*y^2*z^3 + 32*y*z^4 + 6*z^5) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (256 : ℝ) * x^3 * (z - x)^2 + (256 : ℝ) * x^3 * (z - x)^1 * (y - z)^1 + (256 : ℝ) * x^3 * (y - z)^2 + (544 : ℝ) * x^2 * (z - x)^3 + (672 : ℝ) * x^2 * (z - x)^2 * (y - z)^1 + (576 : ℝ) * x^2 * (z - x)^1 * (y - z)^2 + (224 : ℝ) * x^2 * (y - z)^3 + (384 : ℝ) * x^1 * (z - x)^4 + (576 : ℝ) * x^1 * (z - x)^3 * (y - z)^1 + (448 : ℝ) * x^1 * (z - x)^2 * (y - z)^2 + (256 : ℝ) * x^1 * (z - x)^1 * (y - z)^3 + (64 : ℝ) * x^1 * (y - z)^4 + (90 : ℝ) * (z - x)^5 + (162 : ℝ) * (z - x)^4 * (y - z)^1 + (124 : ℝ) * (z - x)^3 * (y - z)^2 + (72 : ℝ) * (z - x)^2 * (y - z)^3 + (32 : ℝ) * (z - x)^1 * (y - z)^4 + (6 : ℝ) * (y - z)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*x^5 + 2*x^4*y + 32*x^4*z + 4*x^3*y^2 - 16*x^3*y*z + 40*x^3*z^2 + 40*x^2*y^3 - 68*x^2*y^2*z - 68*x^2*y*z^2 + 4*x^2*z^3 + 32*x*y^4 - 16*x*y^3*z - 68*x*y^2*z^2 - 16*x*y*z^3 + 2*x*z^4 + 6*y^5 + 2*y^4*z + 4*y^3*z^2 + 40*y^2*z^3 + 32*y*z^4 + 6*z^5) := by
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
  have hn : 0 ≤ (6*x^5 + 2*x^4*y + 32*x^4*z + 4*x^3*y^2 - 16*x^3*y*z + 40*x^3*z^2 + 40*x^2*y^3 - 68*x^2*y^2*z - 68*x^2*y*z^2 + 4*x^2*z^3 + 32*x*y^4 - 16*x*y^3*z - 68*x*y^2*z^2 - 16*x*y*z^3 + 2*x*z^4 + 6*y^5 + 2*y^4*z + 4*y^3*z^2 + 40*y^2*z^3 + 32*y*z^4 + 6*z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 / (3 * x + y) + 1 / (3 * y + z) + 1 / (3 * z + x)) ≥ (1 / (2 * x + y + z) + 1 / (2 * y + z + x) + 1 / (2 * z + x + y))) := @solution
#print axioms solution
