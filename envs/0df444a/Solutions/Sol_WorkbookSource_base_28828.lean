-- Prove2me | solution 1 for WorkbookSource.base_28828
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:08:54.865548+00:00
-- url     : https://prove2.me/submissions/c1a2ee4b-29a0-4155-b62b-76e0156f32a1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 / (x * y + y * z + z * x) + 32 * x * y * z / ((x + y + z) ^ 3 + 5 * x * y * z) ≥ 4  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5 + x^4*y + x^4*z - 2*x^3*y^2 - 3*x^3*y*z - 2*x^3*z^2 - 2*x^2*y^3 + 4*x^2*y^2*z + 4*x^2*y*z^2 - 2*x^2*z^3 + x*y^4 - 3*x*y^3*z + 4*x*y^2*z^2 - 3*x*y*z^3 + x*z^4 + y^5 + y^4*z - 2*y^3*z^2 - 2*y^2*z^3 + y*z^4 + z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * x^3 * (y - x)^2 + (5 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (5 : ℝ) * x^3 * (z - y)^2 + (4 : ℝ) * x^2 * (y - x)^3 + (6 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (24 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (11 : ℝ) * x^2 * (z - y)^3 + (25 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (25 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (7 : ℝ) * x^1 * (z - y)^4 + (8 : ℝ) * (y - x)^3 * (z - y)^2 + (12 : ℝ) * (y - x)^2 * (z - y)^3 + (6 : ℝ) * (y - x)^1 * (z - y)^4 + (1 : ℝ) * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5 + x^4*y + x^4*z - 2*x^3*y^2 - 3*x^3*y*z - 2*x^3*z^2 - 2*x^2*y^3 + 4*x^2*y^2*z + 4*x^2*y*z^2 - 2*x^2*z^3 + x*y^4 - 3*x*y^3*z + 4*x*y^2*z^2 - 3*x*y*z^3 + x*z^4 + y^5 + y^4*z - 2*y^3*z^2 - 2*y^2*z^3 + y*z^4 + z^5) := by
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
  have hn : 0 ≤ (x^5 + x^4*y + x^4*z - 2*x^3*y^2 - 3*x^3*y*z - 2*x^3*z^2 - 2*x^2*y^3 + 4*x^2*y^2*z + 4*x^2*y*z^2 - 2*x^2*z^3 + x*y^4 - 3*x*y^3*z + 4*x*y^2*z^2 - 3*x*y*z^3 + x*z^4 + y^5 + y^4*z - 2*y^3*z^2 - 2*y^2*z^3 + y*z^4 + z^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x + y + z) ^ 2 / (x * y + y * z + z * x) + 32 * x * y * z / ((x + y + z) ^ 3 + 5 * x * y * z) ≥ 4) := @solution
#print axioms solution
