-- Prove2me | solution 1 for WorkbookSource.base_12020
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:39:38.372935+00:00
-- url     : https://prove2.me/submissions/f0ce877d-98aa-4394-9735-499d456e4d1c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (8 / 3 + (3 * x ^ 2 + y * z) / (y ^ 2 + z ^ 2)) * (8 / 3 + (3 * y ^ 2 + z * x) / (z ^ 2 + x ^ 2)) * (8 / 3 + (3 * z ^ 2 + x * y) / (x ^ 2 + y ^ 2)) ≥ 2744 / 27  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (192*x^6 + 72*x^5*y + 72*x^5*z - 336*x^4*y^2 + 91*x^4*y*z - 336*x^4*z^2 + 145*x^3*y^3 + 160*x^3*y^2*z + 160*x^3*y*z^2 + 145*x^3*z^3 - 336*x^2*y^4 + 160*x^2*y^3*z - 660*x^2*y^2*z^2 + 160*x^2*y*z^3 - 336*x^2*z^4 + 72*x*y^5 + 91*x*y^4*z + 160*x*y^3*z^2 + 160*x*y^2*z^3 + 91*x*y*z^4 + 72*x*z^5 + 192*y^6 + 72*y^5*z - 336*y^4*z^2 + 145*y^3*z^3 - 336*y^2*z^4 + 72*y*z^5 + 192*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (1652 : ℝ) * x^4 * (y - x)^2 + (1652 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (1652 : ℝ) * x^4 * (z - y)^2 + (3042 : ℝ) * x^3 * (y - x)^3 + (4563 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (8653 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (3566 : ℝ) * x^3 * (z - y)^3 + (2233 : ℝ) * x^2 * (y - x)^4 + (4466 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (13620 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (11387 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (3019 : ℝ) * x^2 * (z - y)^4 + (652 : ℝ) * x^1 * (y - x)^5 + (1630 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (8638 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (11327 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (6259 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (1296 : ℝ) * x^1 * (z - y)^5 + (1 : ℝ) * (y - x)^6 + (3 : ℝ) * (y - x)^5 * (z - y)^1 + (1683 : ℝ) * (y - x)^4 * (z - y)^2 + (3361 : ℝ) * (y - x)^3 * (z - y)^3 + (2904 : ℝ) * (y - x)^2 * (z - y)^4 + (1224 : ℝ) * (y - x)^1 * (z - y)^5 + (192 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (192*x^6 + 72*x^5*y + 72*x^5*z - 336*x^4*y^2 + 91*x^4*y*z - 336*x^4*z^2 + 145*x^3*y^3 + 160*x^3*y^2*z + 160*x^3*y*z^2 + 145*x^3*z^3 - 336*x^2*y^4 + 160*x^2*y^3*z - 660*x^2*y^2*z^2 + 160*x^2*y*z^3 - 336*x^2*z^4 + 72*x*y^5 + 91*x*y^4*z + 160*x*y^3*z^2 + 160*x*y^2*z^3 + 91*x*y*z^4 + 72*x*z^5 + 192*y^6 + 72*y^5*z - 336*y^4*z^2 + 145*y^3*z^3 - 336*y^2*z^4 + 72*y*z^5 + 192*z^6) := by
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
  have hn : 0 ≤ (192*x^6 + 72*x^5*y + 72*x^5*z - 336*x^4*y^2 + 91*x^4*y*z - 336*x^4*z^2 + 145*x^3*y^3 + 160*x^3*y^2*z + 160*x^3*y*z^2 + 145*x^3*z^3 - 336*x^2*y^4 + 160*x^2*y^3*z - 660*x^2*y^2*z^2 + 160*x^2*y*z^3 - 336*x^2*z^4 + 72*x*y^5 + 91*x*y^4*z + 160*x*y^3*z^2 + 160*x*y^2*z^3 + 91*x*y*z^4 + 72*x*z^5 + 192*y^6 + 72*y^5*z - 336*y^4*z^2 + 145*y^3*z^3 - 336*y^2*z^4 + 72*y*z^5 + 192*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (8 / 3 + (3 * x ^ 2 + y * z) / (y ^ 2 + z ^ 2)) * (8 / 3 + (3 * y ^ 2 + z * x) / (z ^ 2 + x ^ 2)) * (8 / 3 + (3 * z ^ 2 + x * y) / (x ^ 2 + y ^ 2)) ≥ 2744 / 27) := @solution
#print axioms solution
