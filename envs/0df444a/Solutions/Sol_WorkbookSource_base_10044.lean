-- Prove2me | solution 1 for WorkbookSource.base_10044
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:42:35.293935+00:00
-- url     : https://prove2.me/submissions/8b7bd2dd-f8a0-45c6-9bc6-abbfcaaa6e4d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 1) : x * y + y * z + z * x ≥ 8 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)  := by
  have haux (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^5*y + x^5*z - 4*x^4*y^2 + 9*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 + 22*x^3*y^2*z + 22*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 + 22*x^2*y^3*z + 12*x^2*y^2*z^2 + 22*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 9*x*y^4*z + 22*x*y^3*z^2 + 22*x*y^2*z^3 + 9*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (171 : ℝ) * x^6 + (684 : ℝ) * x^5 * (y - x)^1 + (342 : ℝ) * x^5 * (z - y)^1 + (1097 : ℝ) * x^4 * (y - x)^2 + (1097 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (242 : ℝ) * x^4 * (z - y)^2 + (888 : ℝ) * x^3 * (y - x)^3 + (1332 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (604 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (80 : ℝ) * x^3 * (z - y)^3 + (368 : ℝ) * x^2 * (y - x)^4 + (736 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (510 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (142 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (11 : ℝ) * x^2 * (z - y)^4 + (64 : ℝ) * x^1 * (y - x)^5 + (160 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (152 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (68 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (16 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (2 : ℝ) * x^1 * (z - y)^5 + (1 : ℝ) * (y - x)^2 * (z - y)^4 + (1 : ℝ) * (y - x)^1 * (z - y)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^5*y + x^5*z - 4*x^4*y^2 + 9*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 + 22*x^3*y^2*z + 22*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 + 22*x^2*y^3*z + 12*x^2*y^2*z^2 + 22*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 9*x*y^4*z + 22*x*y^3*z^2 + 22*x*y^2*z^3 + 9*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux x z y (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux y x z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux z y x (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-8*x^4*y^2 - 8*x^4*z^2 - 8*x^2*y^4 - 24*x^2*y^2*z^2 - 8*x^2*z^4 + x*y + x*z - 8*y^4*z^2 - 8*y^2*z^4 + y*z) = (x^5*y + x^5*z - 4*x^4*y^2 + 9*x^4*y*z - 4*x^4*z^2 + 6*x^3*y^3 + 22*x^3*y^2*z + 22*x^3*y*z^2 + 6*x^3*z^3 - 4*x^2*y^4 + 22*x^2*y^3*z + 12*x^2*y^2*z^2 + 22*x^2*y*z^3 - 4*x^2*z^4 + x*y^5 + 9*x*y^4*z + 22*x*y^3*z^2 + 22*x*y^2*z^3 + 9*x*y*z^4 + x*z^5 + y^5*z - 4*y^4*z^2 + 6*y^3*z^3 - 4*y^2*z^4 + y*z^5) := by
    linear_combination (-x^4*y - x^4*z - 3*x^3*y^2 - 7*x^3*y*z - x^3*y - 3*x^3*z^2 - x^3*z - 3*x^2*y^3 - 12*x^2*y^2*z - 2*x^2*y^2 - 12*x^2*y*z^2 - 5*x^2*y*z - x^2*y - 3*x^2*z^3 - 2*x^2*z^2 - x^2*z - x*y^4 - 7*x*y^3*z - x*y^3 - 12*x*y^2*z^2 - 5*x*y^2*z - x*y^2 - 7*x*y*z^3 - 5*x*y*z^2 - 3*x*y*z - x*y - x*z^4 - x*z^3 - x*z^2 - x*z - y^4*z - 3*y^3*z^2 - y^3*z - 3*y^2*z^3 - 2*y^2*z^2 - y^2*z - y*z^4 - y*z^3 - y*z^2 - y*z) * h
  nlinarith only [hp, he]
example : (∀ (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 1), x * y + y * z + z * x ≥ 8 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)) := @solution
#print axioms solution
