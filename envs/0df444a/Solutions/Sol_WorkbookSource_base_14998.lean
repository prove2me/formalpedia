-- Prove2me | solution 1 for WorkbookSource.base_14998
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:24.113845+00:00
-- url     : https://prove2.me/submissions/53a23b36-1932-4e44-972d-fb6cf10d6367

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) * (x^7 + y^7 + z^7) ≥ (x^3 + y^3 + z^3) * (x^5 + y^5 + z^5)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^7*y + x^7*z - x^5*y^3 - x^5*z^3 - x^3*y^5 - x^3*z^5 + x*y^7 + x*z^7 + y^7*z - y^5*z^3 - y^3*z^5 + y*z^7) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * x^6 * (y - x)^2 + (16 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (16 : ℝ) * x^6 * (z - y)^2 + (48 : ℝ) * x^5 * (y - x)^3 + (72 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (120 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (48 : ℝ) * x^5 * (z - y)^3 + (60 : ℝ) * x^4 * (y - x)^4 + (120 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (300 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (240 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (60 : ℝ) * x^4 * (z - y)^4 + (40 : ℝ) * x^3 * (y - x)^5 + (100 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (360 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (440 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (220 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (40 : ℝ) * x^3 * (z - y)^5 + (14 : ℝ) * x^2 * (y - x)^6 + (42 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (225 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (380 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (285 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (102 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (14 : ℝ) * x^2 * (z - y)^6 + (2 : ℝ) * x^1 * (y - x)^7 + (7 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (69 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (155 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (155 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (81 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (21 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (2 : ℝ) * x^1 * (z - y)^7 + (8 : ℝ) * (y - x)^6 * (z - y)^2 + (24 : ℝ) * (y - x)^5 * (z - y)^3 + (30 : ℝ) * (y - x)^4 * (z - y)^4 + (20 : ℝ) * (y - x)^3 * (z - y)^5 + (7 : ℝ) * (y - x)^2 * (z - y)^6 + (1 : ℝ) * (y - x)^1 * (z - y)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^7*y + x^7*z - x^5*y^3 - x^5*z^3 - x^3*y^5 - x^3*z^5 + x*y^7 + x*z^7 + y^7*z - y^5*z^3 - y^3*z^5 + y*z^7) := by
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
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x + y + z) * (x^7 + y^7 + z^7) ≥ (x^3 + y^3 + z^3) * (x^5 + y^5 + z^5)) := @solution
#print axioms solution
