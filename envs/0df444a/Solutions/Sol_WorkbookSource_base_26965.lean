-- Prove2me | solution 1 for WorkbookSource.base_26965
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:31.726559+00:00
-- url     : https://prove2.me/submissions/71e0abc6-a63e-4b84-96d8-963713a3b565

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y + x * z) * (x * y + y * z) * (x * z + y * z) ≥ 8 * (y ^ 2 + z ^ 2 - x ^ 2) * (z ^ 2 + x ^ 2 - y ^ 2) * (x ^ 2 + y ^ 2 - z ^ 2) + 64 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (8*x^6 - 72*x^4*y^2 + 128*x^4*y*z - 72*x^4*z^2 + 128*x^3*y^3 - 127*x^3*y^2*z - 127*x^3*y*z^2 + 128*x^3*z^3 - 72*x^2*y^4 - 127*x^2*y^3*z + 402*x^2*y^2*z^2 - 127*x^2*y*z^3 - 72*x^2*z^4 + 128*x*y^4*z - 127*x*y^3*z^2 - 127*x*y^2*z^3 + 128*x*y*z^4 + 8*y^6 - 72*y^4*z^2 + 128*y^3*z^3 - 72*y^2*z^4 + 8*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (34 : ℝ) * x^4 * (y - x)^2 + (34 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (34 : ℝ) * x^4 * (z - y)^2 + (38 : ℝ) * x^3 * (y - x)^3 + (57 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (215 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (98 : ℝ) * x^3 * (z - y)^3 + (14 : ℝ) * x^2 * (y - x)^4 + (28 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (369 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (355 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (104 : ℝ) * x^2 * (z - y)^4 + (2 : ℝ) * x^1 * (y - x)^5 + (5 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (260 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (385 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (224 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (48 : ℝ) * x^1 * (z - y)^5 + (48 : ℝ) * (y - x)^2 * (z - y)^4 + (48 : ℝ) * (y - x)^1 * (z - y)^5 + (8 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*x^6 - 72*x^4*y^2 + 128*x^4*y*z - 72*x^4*z^2 + 128*x^3*y^3 - 127*x^3*y^2*z - 127*x^3*y*z^2 + 128*x^3*z^3 - 72*x^2*y^4 - 127*x^2*y^3*z + 402*x^2*y^2*z^2 - 127*x^2*y*z^3 - 72*x^2*z^4 + 128*x*y^4*z - 127*x*y^3*z^2 - 127*x*y^2*z^3 + 128*x*y*z^4 + 8*y^6 - 72*y^4*z^2 + 128*y^3*z^3 - 72*y^2*z^4 + 8*z^6) := by
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
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x * y + x * z) * (x * y + y * z) * (x * z + y * z) ≥ 8 * (y ^ 2 + z ^ 2 - x ^ 2) * (z ^ 2 + x ^ 2 - y ^ 2) * (x ^ 2 + y ^ 2 - z ^ 2) + 64 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2) := @solution
#print axioms solution
