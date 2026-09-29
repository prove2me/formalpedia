-- Prove2me | solution 1 for WorkbookSource.base_56862
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:45:03.021716+00:00
-- url     : https://prove2.me/submissions/4791347a-8c5c-424b-ba8c-0891fb6e0790

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≤ 3 / (x * y * z)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^7/729 + 7*x^6*y/729 + 7*x^6*z/729 + 7*x^5*y^2/243 + 14*x^5*y*z/243 + 7*x^5*z^2/243 + 35*x^4*y^3/729 + 35*x^4*y^2*z/243 + 35*x^4*y*z^2/243 + 35*x^4*z^3/729 + 35*x^3*y^4/729 - 589*x^3*y^3*z/729 + 70*x^3*y^2*z^2/243 - 589*x^3*y*z^3/729 + 35*x^3*z^4/729 + 7*x^2*y^5/243 + 35*x^2*y^4*z/243 + 70*x^2*y^3*z^2/243 + 70*x^2*y^2*z^3/243 + 35*x^2*y*z^4/243 + 7*x^2*z^5/243 + 7*x*y^6/729 + 14*x*y^5*z/243 + 35*x*y^4*z^2/243 - 589*x*y^3*z^3/729 + 35*x*y^2*z^4/243 + 14*x*y*z^5/243 + 7*x*z^6/729 + y^7/729 + 7*y^6*z/729 + 7*y^5*z^2/243 + 35*y^4*z^3/729 + 35*y^3*z^4/729 + 7*y^2*z^5/243 + 7*y*z^6/729 + z^7/729) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * x^5 * (y - x)^2 + (1 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (1 : ℝ) * x^5 * (z - y)^2 + (28/9 : ℝ) * x^4 * (y - x)^3 + (14/3 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (16/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (17/9 : ℝ) * x^4 * (z - y)^3 + (101/27 : ℝ) * x^3 * (y - x)^4 + (202/27 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (91/9 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (172/27 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (35/27 : ℝ) * x^3 * (z - y)^4 + (62/27 : ℝ) * x^2 * (y - x)^5 + (155/27 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (236/27 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (199/27 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (70/27 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (7/27 : ℝ) * x^2 * (z - y)^5 + (205/243 : ℝ) * x^1 * (y - x)^6 + (205/81 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (317/81 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (877/243 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (140/81 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (28/81 : ℝ) * x^1 * (y - x)^1 * (z - y)^5 + (7/243 : ℝ) * x^1 * (z - y)^6 + (128/729 : ℝ) * (y - x)^7 + (448/729 : ℝ) * (y - x)^6 * (z - y)^1 + (224/243 : ℝ) * (y - x)^5 * (z - y)^2 + (560/729 : ℝ) * (y - x)^4 * (z - y)^3 + (280/729 : ℝ) * (y - x)^3 * (z - y)^4 + (28/243 : ℝ) * (y - x)^2 * (z - y)^5 + (14/729 : ℝ) * (y - x)^1 * (z - y)^6 + (1/729 : ℝ) * (z - y)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^7/729 + 7*x^6*y/729 + 7*x^6*z/729 + 7*x^5*y^2/243 + 14*x^5*y*z/243 + 7*x^5*z^2/243 + 35*x^4*y^3/729 + 35*x^4*y^2*z/243 + 35*x^4*y*z^2/243 + 35*x^4*z^3/729 + 35*x^3*y^4/729 - 589*x^3*y^3*z/729 + 70*x^3*y^2*z^2/243 - 589*x^3*y*z^3/729 + 35*x^3*z^4/729 + 7*x^2*y^5/243 + 35*x^2*y^4*z/243 + 70*x^2*y^3*z^2/243 + 70*x^2*y^2*z^3/243 + 35*x^2*y*z^4/243 + 7*x^2*z^5/243 + 7*x*y^6/729 + 14*x*y^5*z/243 + 35*x*y^4*z^2/243 - 589*x*y^3*z^3/729 + 35*x*y^2*z^4/243 + 14*x*y*z^5/243 + 7*x*z^6/729 + y^7/729 + 7*y^6*z/729 + 7*y^5*z^2/243 + 35*y^4*z^3/729 + 35*y^3*z^4/729 + 7*y^2*z^5/243 + 7*y*z^6/729 + z^7/729) := by
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
  have he : (-x^3*y^3*z - x^3*y*z^3 - x*y^3*z^3 + 3) = (x^7/729 + 7*x^6*y/729 + 7*x^6*z/729 + 7*x^5*y^2/243 + 14*x^5*y*z/243 + 7*x^5*z^2/243 + 35*x^4*y^3/729 + 35*x^4*y^2*z/243 + 35*x^4*y*z^2/243 + 35*x^4*z^3/729 + 35*x^3*y^4/729 - 589*x^3*y^3*z/729 + 70*x^3*y^2*z^2/243 - 589*x^3*y*z^3/729 + 35*x^3*z^4/729 + 7*x^2*y^5/243 + 35*x^2*y^4*z/243 + 70*x^2*y^3*z^2/243 + 70*x^2*y^2*z^3/243 + 35*x^2*y*z^4/243 + 7*x^2*z^5/243 + 7*x*y^6/729 + 14*x*y^5*z/243 + 35*x*y^4*z^2/243 - 589*x*y^3*z^3/729 + 35*x*y^2*z^4/243 + 14*x*y*z^5/243 + 7*x*z^6/729 + y^7/729 + 7*y^6*z/729 + 7*y^5*z^2/243 + 35*y^4*z^3/729 + 35*y^3*z^4/729 + 7*y^2*z^5/243 + 7*y*z^6/729 + z^7/729) := by
    linear_combination (-x^6/729 - 2*x^5*y/243 - 2*x^5*z/243 - x^5/243 - 5*x^4*y^2/243 - 10*x^4*y*z/243 - 5*x^4*y/243 - 5*x^4*z^2/243 - 5*x^4*z/243 - x^4/81 - 20*x^3*y^3/729 - 20*x^3*y^2*z/243 - 10*x^3*y^2/243 - 20*x^3*y*z^2/243 - 20*x^3*y*z/243 - 4*x^3*y/81 - 20*x^3*z^3/729 - 10*x^3*z^2/243 - 4*x^3*z/81 - x^3/27 - 5*x^2*y^4/243 - 20*x^2*y^3*z/243 - 10*x^2*y^3/243 - 10*x^2*y^2*z^2/81 - 10*x^2*y^2*z/81 - 2*x^2*y^2/27 - 20*x^2*y*z^3/243 - 10*x^2*y*z^2/81 - 4*x^2*y*z/27 - x^2*y/9 - 5*x^2*z^4/243 - 10*x^2*z^3/243 - 2*x^2*z^2/27 - x^2*z/9 - x^2/9 - 2*x*y^5/243 - 10*x*y^4*z/243 - 5*x*y^4/243 - 20*x*y^3*z^2/243 - 20*x*y^3*z/243 - 4*x*y^3/81 - 20*x*y^2*z^3/243 - 10*x*y^2*z^2/81 - 4*x*y^2*z/27 - x*y^2/9 - 10*x*y*z^4/243 - 20*x*y*z^3/243 - 4*x*y*z^2/27 - 2*x*y*z/9 - 2*x*y/9 - 2*x*z^5/243 - 5*x*z^4/243 - 4*x*z^3/81 - x*z^2/9 - 2*x*z/9 - x/3 - y^6/729 - 2*y^5*z/243 - y^5/243 - 5*y^4*z^2/243 - 5*y^4*z/243 - y^4/81 - 20*y^3*z^3/729 - 10*y^3*z^2/243 - 4*y^3*z/81 - y^3/27 - 5*y^2*z^4/243 - 10*y^2*z^3/243 - 2*y^2*z^2/27 - y^2*z/9 - y^2/9 - 2*y*z^5/243 - 5*y*z^4/243 - 4*y*z^3/81 - y*z^2/9 - 2*y*z/9 - y/3 - z^6/729 - z^5/243 - z^4/81 - z^3/27 - z^2/9 - z/3 - 1) * h
  have hn : 0 ≤ (-x^3*y^3*z - x^3*y*z^3 - x*y^3*z^3 + 3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≤ 3 / (x * y * z)) := @solution
#print axioms solution
