-- Prove2me | solution 1 for WorkbookSource.base_16299
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:03:47.910935+00:00
-- url     : https://prove2.me/submissions/a65db062-cacd-43ac-8a8f-567298487b07

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) ^ 2 + y / (z + x) ^ 2 + z / (x + y) ^ 2) ≥ 9 / (4 * (x + y + z))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^6 + 12*x^5*y + 12*x^5*z + 3*x^4*y^2 + 14*x^4*y*z + 3*x^4*z^2 - 10*x^3*y^3 - 14*x^3*y^2*z - 14*x^3*y*z^2 - 10*x^3*z^3 + 3*x^2*y^4 - 14*x^2*y^3*z - 30*x^2*y^2*z^2 - 14*x^2*y*z^3 + 3*x^2*z^4 + 12*x*y^5 + 14*x*y^4*z - 14*x*y^3*z^2 - 14*x*y^2*z^3 + 14*x*y*z^4 + 12*x*z^5 + 4*y^6 + 12*y^5*z + 3*y^4*z^2 - 10*y^3*z^3 + 3*y^2*z^4 + 12*y*z^5 + 4*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (224 : ℝ) * x^4 * (y - x)^2 + (224 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (224 : ℝ) * x^4 * (z - y)^2 + (544 : ℝ) * x^3 * (y - x)^3 + (816 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (976 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (352 : ℝ) * x^3 * (z - y)^3 + (488 : ℝ) * x^2 * (y - x)^4 + (976 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (1416 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (928 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (200 : ℝ) * x^2 * (z - y)^4 + (192 : ℝ) * x^1 * (y - x)^5 + (480 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (832 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (768 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (320 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (48 : ℝ) * x^1 * (z - y)^5 + (28 : ℝ) * (y - x)^6 + (84 : ℝ) * (y - x)^5 * (z - y)^1 + (171 : ℝ) * (y - x)^4 * (z - y)^2 + (202 : ℝ) * (y - x)^3 * (z - y)^3 + (123 : ℝ) * (y - x)^2 * (z - y)^4 + (36 : ℝ) * (y - x)^1 * (z - y)^5 + (4 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^6 + 12*x^5*y + 12*x^5*z + 3*x^4*y^2 + 14*x^4*y*z + 3*x^4*z^2 - 10*x^3*y^3 - 14*x^3*y^2*z - 14*x^3*y*z^2 - 10*x^3*z^3 + 3*x^2*y^4 - 14*x^2*y^3*z - 30*x^2*y^2*z^2 - 14*x^2*y*z^3 + 3*x^2*z^4 + 12*x*y^5 + 14*x*y^4*z - 14*x*y^3*z^2 - 14*x*y^2*z^3 + 14*x*y*z^4 + 12*x*z^5 + 4*y^6 + 12*y^5*z + 3*y^4*z^2 - 10*y^3*z^3 + 3*y^2*z^4 + 12*y*z^5 + 4*z^6) := by
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
  have hn : 0 ≤ (4*x^6 + 12*x^5*y + 12*x^5*z + 3*x^4*y^2 + 14*x^4*y*z + 3*x^4*z^2 - 10*x^3*y^3 - 14*x^3*y^2*z - 14*x^3*y*z^2 - 10*x^3*z^3 + 3*x^2*y^4 - 14*x^2*y^3*z - 30*x^2*y^2*z^2 - 14*x^2*y*z^3 + 3*x^2*z^4 + 12*x*y^5 + 14*x*y^4*z - 14*x*y^3*z^2 - 14*x*y^2*z^3 + 14*x*y*z^4 + 12*x*z^5 + 4*y^6 + 12*y^5*z + 3*y^4*z^2 - 10*y^3*z^3 + 3*y^2*z^4 + 12*y*z^5 + 4*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x / (y + z) ^ 2 + y / (z + x) ^ 2 + z / (x + y) ^ 2) ≥ 9 / (4 * (x + y + z))) := @solution
#print axioms solution
