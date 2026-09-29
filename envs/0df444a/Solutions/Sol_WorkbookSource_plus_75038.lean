-- Prove2me | solution 1 for WorkbookSource.plus_75038
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:38.683772+00:00
-- url     : https://prove2.me/submissions/7eb0a580-8993-4abe-98e9-1d8a9df970b8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x + y + z = 3) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) : 2 * (x ^ 2 + y ^ 2 + z ^ 2) + x ^ 2 * z + x * y ^ 2 + y * z ^ 2 ≥ 2 * x * y * z + x * y + y * z + x * z + 4   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (14*x^3/27 - x^2*y/9 + 8*x^2*z/9 + 8*x*y^2/9 - 35*x*y*z/9 - x*z^2/9 + 14*y^3/27 - y^2*z/9 + 8*y*z^2/9 + 14*z^3/27) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (7/3 : ℝ) * x^1 * (y - x)^2 + (7/3 : ℝ) * x^1 * (y - x)^1 * (z - y)^1 + (7/3 : ℝ) * x^1 * (z - y)^2 + (49/27 : ℝ) * (y - x)^3 + (29/9 : ℝ) * (y - x)^2 * (z - y)^1 + (22/9 : ℝ) * (y - x)^1 * (z - y)^2 + (14/27 : ℝ) * (z - y)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (14*x^3/27 - x^2*y/9 + 8*x^2*z/9 + 8*x*y^2/9 - 35*x*y*z/9 - x*z^2/9 + 14*y^3/27 - y^2*z/9 + 8*y*z^2/9 + 14*z^3/27) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (7/3 : ℝ) * x^1 * (z - x)^2 + (7/3 : ℝ) * x^1 * (z - x)^1 * (y - z)^1 + (7/3 : ℝ) * x^1 * (y - z)^2 + (49/27 : ℝ) * (z - x)^3 + (20/9 : ℝ) * (z - x)^2 * (y - z)^1 + (13/9 : ℝ) * (z - x)^1 * (y - z)^2 + (14/27 : ℝ) * (y - z)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (14*x^3/27 - x^2*y/9 + 8*x^2*z/9 + 8*x*y^2/9 - 35*x*y*z/9 - x*z^2/9 + 14*y^3/27 - y^2*z/9 + 8*y*z^2/9 + 14*z^3/27) := by
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
  have he : (x^2*z + 2*x^2 + x*y^2 - 2*x*y*z - x*y - x*z + 2*y^2 + y*z^2 - y*z + 2*z^2 - 4) = (14*x^3/27 - x^2*y/9 + 8*x^2*z/9 + 8*x*y^2/9 - 35*x*y*z/9 - x*z^2/9 + 14*y^3/27 - y^2*z/9 + 8*y*z^2/9 + 14*z^3/27) := by
    linear_combination (-14*x^2/27 + 17*x*y/27 + 17*x*z/27 + 4*x/9 - 14*y^2/27 + 17*y*z/27 + 4*y/9 - 14*z^2/27 + 4*z/9 + 4/3) * hx
  nlinarith only [hp, he]
example : (∀ (x y z : ℝ) (hx : x + y + z = 3) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z), 2 * (x ^ 2 + y ^ 2 + z ^ 2) + x ^ 2 * z + x * y ^ 2 + y * z ^ 2 ≥ 2 * x * y * z + x * y + y * z + x * z + 4) := @solution
#print axioms solution
