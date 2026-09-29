-- Prove2me | solution 1 for WorkbookSource.base_6114
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:44.339758+00:00
-- url     : https://prove2.me/submissions/9c822e70-fb12-4dec-82a0-bdfc4910add2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x * y + y * z + z * x + x * y * z = 4) : (x * y) / (2 * x + 3 * y) + (y * z) / (2 * y + 3 * z) + (z * x) / (2 * z + 3 * x) ≤ (1 / 5) * (x + y + z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (12*x^3*y + 18*x^3*z - 30*x^2*y*z + 18*x*y^3 - 30*x*y^2*z - 30*x*y*z^2 + 12*x*z^3 + 12*y^3*z + 18*y*z^3) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (60 : ℝ) * x^2 * (y - x)^2 + (60 : ℝ) * x^2 * (y - x)^1 * (z - y)^1 + (60 : ℝ) * x^2 * (z - y)^2 + (90 : ℝ) * x^1 * (y - x)^3 + (144 : ℝ) * x^1 * (y - x)^2 * (z - y)^1 + (114 : ℝ) * x^1 * (y - x)^1 * (z - y)^2 + (30 : ℝ) * x^1 * (z - y)^3 + (30 : ℝ) * (y - x)^4 + (66 : ℝ) * (y - x)^3 * (z - y)^1 + (54 : ℝ) * (y - x)^2 * (z - y)^2 + (18 : ℝ) * (y - x)^1 * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (12*x^3*y + 18*x^3*z - 30*x^2*y*z + 18*x*y^3 - 30*x*y^2*z - 30*x*y*z^2 + 12*x*z^3 + 12*y^3*z + 18*y*z^3) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (60 : ℝ) * x^2 * (z - x)^2 + (60 : ℝ) * x^2 * (z - x)^1 * (y - z)^1 + (60 : ℝ) * x^2 * (y - z)^2 + (90 : ℝ) * x^1 * (z - x)^3 + (126 : ℝ) * x^1 * (z - x)^2 * (y - z)^1 + (96 : ℝ) * x^1 * (z - x)^1 * (y - z)^2 + (30 : ℝ) * x^1 * (y - z)^3 + (30 : ℝ) * (z - x)^4 + (54 : ℝ) * (z - x)^3 * (y - z)^1 + (36 : ℝ) * (z - x)^2 * (y - z)^2 + (12 : ℝ) * (z - x)^1 * (y - z)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*x^3*y + 18*x^3*z - 30*x^2*y*z + 18*x*y^3 - 30*x*y^2*z - 30*x*y*z^2 + 12*x*z^3 + 12*y^3*z + 18*y*z^3) := by
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
  have hn : 0 ≤ (12*x^3*y + 18*x^3*z - 30*x^2*y*z + 18*x*y^3 - 30*x*y^2*z - 30*x*y*z^2 + 12*x*z^3 + 12*y^3*z + 18*y*z^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x * y + y * z + z * x + x * y * z = 4), (x * y) / (2 * x + 3 * y) + (y * z) / (2 * y + 3 * z) + (z * x) / (2 * z + 3 * x) ≤ (1 / 5) * (x + y + z)) := @solution
#print axioms solution
