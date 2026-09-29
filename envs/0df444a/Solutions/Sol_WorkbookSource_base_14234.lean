-- Prove2me | solution 1 for WorkbookSource.base_14234
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:55:07.91064+00:00
-- url     : https://prove2.me/submissions/39028557-d35f-4c6b-80d7-b9615ee6f1e6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (8 * x * y * z) / (x + y) / (y + z) / (z + x) ≤ (3 * (x ^ 2 + y ^ 2 + z ^ 2 + 3 * (x * y + y * z + z * x))) / (4 * (x + y + z) ^ 2)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^4*y + 3*x^4*z + 12*x^3*y^2 - 8*x^3*y*z + 12*x^3*z^2 + 12*x^2*y^3 - 22*x^2*y^2*z - 22*x^2*y*z^2 + 12*x^2*z^3 + 3*x*y^4 - 8*x*y^3*z - 22*x*y^2*z^2 - 8*x*y*z^3 + 3*x*z^4 + 3*y^4*z + 12*y^3*z^2 + 12*y^2*z^3 + 3*y*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * x^3 * (y - x)^2 + (64 : ℝ) * x^3 * (y - x)^1 * (z - y)^1 + (64 : ℝ) * x^3 * (z - y)^2 + (152 : ℝ) * x^2 * (y - x)^3 + (228 : ℝ) * x^2 * (y - x)^2 * (z - y)^1 + (156 : ℝ) * x^2 * (y - x)^1 * (z - y)^2 + (40 : ℝ) * x^2 * (z - y)^3 + (118 : ℝ) * x^1 * (y - x)^4 + (236 : ℝ) * x^1 * (y - x)^3 * (z - y)^1 + (170 : ℝ) * x^1 * (y - x)^2 * (z - y)^2 + (52 : ℝ) * x^1 * (y - x)^1 * (z - y)^3 + (6 : ℝ) * x^1 * (z - y)^4 + (30 : ℝ) * (y - x)^5 + (75 : ℝ) * (y - x)^4 * (z - y)^1 + (66 : ℝ) * (y - x)^3 * (z - y)^2 + (24 : ℝ) * (y - x)^2 * (z - y)^3 + (3 : ℝ) * (y - x)^1 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^4*y + 3*x^4*z + 12*x^3*y^2 - 8*x^3*y*z + 12*x^3*z^2 + 12*x^2*y^3 - 22*x^2*y^2*z - 22*x^2*y*z^2 + 12*x^2*z^3 + 3*x*y^4 - 8*x*y^3*z - 22*x*y^2*z^2 - 8*x*y*z^3 + 3*x*z^4 + 3*y^4*z + 12*y^3*z^2 + 12*y^2*z^3 + 3*y*z^4) := by
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
  have hn : 0 ≤ (3*x^4*y + 3*x^4*z + 12*x^3*y^2 - 8*x^3*y*z + 12*x^3*z^2 + 12*x^2*y^3 - 22*x^2*y^2*z - 22*x^2*y*z^2 + 12*x^2*z^3 + 3*x*y^4 - 8*x*y^3*z - 22*x*y^2*z^2 - 8*x*y*z^3 + 3*x*z^4 + 3*y^4*z + 12*y^3*z^2 + 12*y^2*z^3 + 3*y*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (8 * x * y * z) / (x + y) / (y + z) / (z + x) ≤ (3 * (x ^ 2 + y ^ 2 + z ^ 2 + 3 * (x * y + y * z + z * x))) / (4 * (x + y + z) ^ 2)) := @solution
#print axioms solution
