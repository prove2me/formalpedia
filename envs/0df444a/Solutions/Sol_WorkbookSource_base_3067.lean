-- Prove2me | solution 1 for WorkbookSource.base_3067
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:09:13.370423+00:00
-- url     : https://prove2.me/submissions/cd1cdb81-3f13-4960-bacd-f26dcbd657a3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 6 * z * y + 6 * x * z + 6 * y * x ≤ 8 * (x + y + z) * x * y * z / ((y + z) * (z + 2 * x + y)) + 8 * (x + y + z) * x * y * z / ((z + x) * (x + 2 * y + z)) + 8 * (x + y + z) * x * y * z / ((x + y) * (y + 2 * z + x)) + 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (6*x^7*y + 6*x^7*z + 15*x^6*y^2 + 38*x^6*y*z + 15*x^6*z^2 - 6*x^5*y^3 + 42*x^5*y^2*z + 42*x^5*y*z^2 - 6*x^5*z^3 - 30*x^4*y^4 - 38*x^4*y^3*z - 38*x^4*y*z^3 - 30*x^4*z^4 - 6*x^3*y^5 - 38*x^3*y^4*z - 46*x^3*y^3*z^2 - 46*x^3*y^2*z^3 - 38*x^3*y*z^4 - 6*x^3*z^5 + 15*x^2*y^6 + 42*x^2*y^5*z - 46*x^2*y^3*z^3 + 42*x^2*y*z^5 + 15*x^2*z^6 + 6*x*y^7 + 38*x*y^6*z + 42*x*y^5*z^2 - 38*x*y^4*z^3 - 38*x*y^3*z^4 + 42*x*y^2*z^5 + 38*x*y*z^6 + 6*x*z^7 + 6*y^7*z + 15*y^6*z^2 - 6*y^5*z^3 - 30*y^4*z^4 - 6*y^3*z^5 + 15*y^2*z^6 + 6*y*z^7) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (704 : ℝ) * x^6 * (y - x)^2 + (704 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (704 : ℝ) * x^6 * (z - y)^2 + (2448 : ℝ) * x^5 * (y - x)^3 + (3672 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (4776 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (1776 : ℝ) * x^5 * (z - y)^3 + (3344 : ℝ) * x^4 * (y - x)^4 + (6688 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (11112 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (7768 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (1664 : ℝ) * x^4 * (z - y)^4 + (2244 : ℝ) * x^3 * (y - x)^5 + (5610 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (11876 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (12204 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (5158 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (732 : ℝ) * x^3 * (z - y)^5 + (740 : ℝ) * x^2 * (y - x)^6 + (2220 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (6207 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (8714 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (5541 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (1554 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (152 : ℝ) * x^2 * (z - y)^6 + (96 : ℝ) * x^1 * (y - x)^7 + (336 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (1464 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (2820 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (2452 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (1026 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (194 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (12 : ℝ) * x^1 * (z - y)^7 + (108 : ℝ) * (y - x)^6 * (z - y)^2 + (324 : ℝ) * (y - x)^5 * (z - y)^3 + (375 : ℝ) * (y - x)^4 * (z - y)^4 + (210 : ℝ) * (y - x)^3 * (z - y)^5 + (57 : ℝ) * (y - x)^2 * (z - y)^6 + (6 : ℝ) * (y - x)^1 * (z - y)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*x^7*y + 6*x^7*z + 15*x^6*y^2 + 38*x^6*y*z + 15*x^6*z^2 - 6*x^5*y^3 + 42*x^5*y^2*z + 42*x^5*y*z^2 - 6*x^5*z^3 - 30*x^4*y^4 - 38*x^4*y^3*z - 38*x^4*y*z^3 - 30*x^4*z^4 - 6*x^3*y^5 - 38*x^3*y^4*z - 46*x^3*y^3*z^2 - 46*x^3*y^2*z^3 - 38*x^3*y*z^4 - 6*x^3*z^5 + 15*x^2*y^6 + 42*x^2*y^5*z - 46*x^2*y^3*z^3 + 42*x^2*y*z^5 + 15*x^2*z^6 + 6*x*y^7 + 38*x*y^6*z + 42*x*y^5*z^2 - 38*x*y^4*z^3 - 38*x*y^3*z^4 + 42*x*y^2*z^5 + 38*x*y*z^6 + 6*x*z^7 + 6*y^7*z + 15*y^6*z^2 - 6*y^5*z^3 - 30*y^4*z^4 - 6*y^3*z^5 + 15*y^2*z^6 + 6*y*z^7) := by
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
  have hn : 0 ≤ (6*x^7*y + 6*x^7*z + 15*x^6*y^2 + 38*x^6*y*z + 15*x^6*z^2 - 6*x^5*y^3 + 42*x^5*y^2*z + 42*x^5*y*z^2 - 6*x^5*z^3 - 30*x^4*y^4 - 38*x^4*y^3*z - 38*x^4*y*z^3 - 30*x^4*z^4 - 6*x^3*y^5 - 38*x^3*y^4*z - 46*x^3*y^3*z^2 - 46*x^3*y^2*z^3 - 38*x^3*y*z^4 - 6*x^3*z^5 + 15*x^2*y^6 + 42*x^2*y^5*z - 46*x^2*y^3*z^3 + 42*x^2*y*z^5 + 15*x^2*z^6 + 6*x*y^7 + 38*x*y^6*z + 42*x*y^5*z^2 - 38*x*y^4*z^3 - 38*x*y^3*z^4 + 42*x*y^2*z^5 + 38*x*y*z^6 + 6*x*z^7 + 6*y^7*z + 15*y^6*z^2 - 6*y^5*z^3 - 30*y^4*z^4 - 6*y^3*z^5 + 15*y^2*z^6 + 6*y*z^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 6 * z * y + 6 * x * z + 6 * y * x ≤ 8 * (x + y + z) * x * y * z / ((y + z) * (z + 2 * x + y)) + 8 * (x + y + z) * x * y * z / ((z + x) * (x + 2 * y + z)) + 8 * (x + y + z) * x * y * z / ((x + y) * (y + 2 * z + x)) + 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2) := @solution
#print axioms solution
