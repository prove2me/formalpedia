-- Prove2me | solution 1 for WorkbookSource.base_8376
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:38:17.890777+00:00
-- url     : https://prove2.me/submissions/2fc6f232-d695-41e3-be89-0e157427053c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≤ (3 * (x + y + z)) / (2 * (x * y + y * z + z * x)) - (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) / (4 * (x * y + y * z + z * x) * (x + y + z))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^4*y + x^4*z + 2*x^3*y^2 + 2*x^3*z^2 + 2*x^2*y^3 - 6*x^2*y^2*z - 6*x^2*y*z^2 + 2*x^2*z^3 + x*y^4 - 6*x*y^2*z^2 + x*z^4 + y^4*z + 2*y^3*z^2 + 2*y^2*z^3 + y*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * x^3 * (y - x)^2 + (16 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (16 : ℝ) * x^3 * (z - y)^2 + (36 : ℝ) * x^2 * (y - x)^3 + (54 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (42 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (12 : ℝ) * x^2 * (z - y)^3 + (26 : ℝ) * x^1 * (y - x)^4 + (52 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (42 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (16 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (2 : ℝ) * x^1 * (z - y)^4 + (6 : ℝ) * (y - x)^5 + (15 : ℝ) * (y - x)^4 * (z - y)^1 + (14 : ℝ) * (y - x)^3 * (z - y)^2 + (6 : ℝ) * (y - x)^2 * (z - y)^3 + (1 : ℝ) * (y - x)^1 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^4*y + x^4*z + 2*x^3*y^2 + 2*x^3*z^2 + 2*x^2*y^3 - 6*x^2*y^2*z - 6*x^2*y*z^2 + 2*x^2*z^3 + x*y^4 - 6*x*y^2*z^2 + x*z^4 + y^4*z + 2*y^3*z^2 + 2*y^2*z^3 + y*z^4) := by
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
  have hn : 0 ≤ (x^4*y + x^4*z + 2*x^3*y^2 + 2*x^3*z^2 + 2*x^2*y^3 - 6*x^2*y^2*z - 6*x^2*y*z^2 + 2*x^2*z^3 + x*y^4 - 6*x*y^2*z^2 + x*z^4 + y^4*z + 2*y^3*z^2 + 2*y^2*z^3 + y*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≤ (3 * (x + y + z)) / (2 * (x * y + y * z + z * x)) - (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) / (4 * (x * y + y * z + z * x) * (x + y + z))) := @solution
#print axioms solution
