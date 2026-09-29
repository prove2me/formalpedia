-- Prove2me | solution 1 for WorkbookSource.base_6511
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:19:10.335958+00:00
-- url     : https://prove2.me/submissions/77b15395-c8f1-4120-805a-7eb3b9c70dd4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 2 * (3 / (x ^ 2 + y ^ 2 + z ^ 2) + 1 / x ^ 2 + 1 / y ^ 2 + 1 / z ^ 2) ≥ 36  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6*y^2 + x^6*z^2 + 2*x^5*y^3 + 2*x^5*y^2*z + 2*x^5*y*z^2 + 2*x^5*z^3 + 2*x^4*y^4 + 2*x^4*y^3*z - 28*x^4*y^2*z^2 + 2*x^4*y*z^3 + 2*x^4*z^4 + 2*x^3*y^5 + 2*x^3*y^4*z + 12*x^3*y^3*z^2 + 12*x^3*y^2*z^3 + 2*x^3*y*z^4 + 2*x^3*z^5 + x^2*y^6 + 2*x^2*y^5*z - 28*x^2*y^4*z^2 + 12*x^2*y^3*z^3 - 28*x^2*y^2*z^4 + 2*x^2*y*z^5 + x^2*z^6 + 2*x*y^5*z^2 + 2*x*y^4*z^3 + 2*x*y^3*z^4 + 2*x*y^2*z^5 + y^6*z^2 + 2*y^5*z^3 + 2*y^4*z^4 + 2*y^3*z^5 + y^2*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (48 : ℝ) * x^6 * (y - x)^2 + (48 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (48 : ℝ) * x^6 * (z - y)^2 + (216 : ℝ) * x^5 * (y - x)^3 + (324 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (252 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (72 : ℝ) * x^5 * (z - y)^3 + (410 : ℝ) * x^4 * (y - x)^4 + (820 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (690 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (280 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (50 : ℝ) * x^4 * (z - y)^4 + (420 : ℝ) * x^3 * (y - x)^5 + (1050 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (1060 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (540 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (150 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (20 : ℝ) * x^3 * (z - y)^5 + (242 : ℝ) * x^2 * (y - x)^6 + (726 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (885 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (560 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (195 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (36 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (2 : ℝ) * x^2 * (z - y)^6 + (72 : ℝ) * x^1 * (y - x)^7 + (252 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (364 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (280 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (120 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (26 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (2 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (8 : ℝ) * (y - x)^8 + (32 : ℝ) * (y - x)^7 * (z - y)^1 + (54 : ℝ) * (y - x)^6 * (z - y)^2 + (50 : ℝ) * (y - x)^5 * (z - y)^3 + (27 : ℝ) * (y - x)^4 * (z - y)^4 + (8 : ℝ) * (y - x)^3 * (z - y)^5 + (1 : ℝ) * (y - x)^2 * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6*y^2 + x^6*z^2 + 2*x^5*y^3 + 2*x^5*y^2*z + 2*x^5*y*z^2 + 2*x^5*z^3 + 2*x^4*y^4 + 2*x^4*y^3*z - 28*x^4*y^2*z^2 + 2*x^4*y*z^3 + 2*x^4*z^4 + 2*x^3*y^5 + 2*x^3*y^4*z + 12*x^3*y^3*z^2 + 12*x^3*y^2*z^3 + 2*x^3*y*z^4 + 2*x^3*z^5 + x^2*y^6 + 2*x^2*y^5*z - 28*x^2*y^4*z^2 + 12*x^2*y^3*z^3 - 28*x^2*y^2*z^4 + 2*x^2*y*z^5 + x^2*z^6 + 2*x*y^5*z^2 + 2*x*y^4*z^3 + 2*x*y^3*z^4 + 2*x*y^2*z^5 + y^6*z^2 + 2*y^5*z^3 + 2*y^4*z^4 + 2*y^3*z^5 + y^2*z^6) := by
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
  have hn : 0 ≤ (x^6*y^2 + x^6*z^2 + 2*x^5*y^3 + 2*x^5*y^2*z + 2*x^5*y*z^2 + 2*x^5*z^3 + 2*x^4*y^4 + 2*x^4*y^3*z - 28*x^4*y^2*z^2 + 2*x^4*y*z^3 + 2*x^4*z^4 + 2*x^3*y^5 + 2*x^3*y^4*z + 12*x^3*y^3*z^2 + 12*x^3*y^2*z^3 + 2*x^3*y*z^4 + 2*x^3*z^5 + x^2*y^6 + 2*x^2*y^5*z - 28*x^2*y^4*z^2 + 12*x^2*y^3*z^3 - 28*x^2*y^2*z^4 + 2*x^2*y*z^5 + x^2*z^6 + 2*x*y^5*z^2 + 2*x*y^4*z^3 + 2*x*y^3*z^4 + 2*x*y^2*z^5 + y^6*z^2 + 2*y^5*z^3 + 2*y^4*z^4 + 2*y^3*z^5 + y^2*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), (x + y + z) ^ 2 * (3 / (x ^ 2 + y ^ 2 + z ^ 2) + 1 / x ^ 2 + 1 / y ^ 2 + 1 / z ^ 2) ≥ 36) := @solution
#print axioms solution
