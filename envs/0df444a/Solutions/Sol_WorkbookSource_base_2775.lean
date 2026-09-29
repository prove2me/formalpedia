-- Prove2me | solution 1 for WorkbookSource.base_2775
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:03:15.085565+00:00
-- url     : https://prove2.me/submissions/8b887b8d-7917-4915-a3b4-ff7c8e5ada57

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (y^3 * z^3 + 2) / (y * z) + (z^3 * x^3 + 2) / (z * x) + (x^3 * y^3 + 2) / (x * y) ≥ (x^2 + 2) / x + (y^2 + 2) / y + (z^2 + 2) / z  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^7/729 + 8*x^6*y/729 + 8*x^6*z/729 + 4*x^5*y^2/243 - x^5*y*z/81 + 4*x^5*z^2/243 + 10*x^4*y^3/729 - 4*x^4*y^2*z/27 - 4*x^4*y*z^2/27 + 10*x^4*z^3/729 + 10*x^3*y^4/729 + 547*x^3*y^3*z/729 - 128*x^3*y^2*z^2/243 + 547*x^3*y*z^3/729 + 10*x^3*z^4/729 + 4*x^2*y^5/243 - 4*x^2*y^4*z/27 - 128*x^2*y^3*z^2/243 - 128*x^2*y^2*z^3/243 - 4*x^2*y*z^4/27 + 4*x^2*z^5/243 + 8*x*y^6/729 - x*y^5*z/81 - 4*x*y^4*z^2/27 + 547*x*y^3*z^3/729 - 4*x*y^2*z^4/27 - x*y*z^5/81 + 8*x*z^6/729 + 2*y^7/729 + 8*y^6*z/729 + 4*y^5*z^2/243 + 10*y^4*z^3/729 + 10*y^3*z^4/729 + 4*y^2*z^5/243 + 8*y*z^6/729 + 2*z^7/729) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * x^5 * (y - x)^2 + (2/3 : ℝ) * x^5 * (y - x)^1 * (z - y)^1 + (2/3 : ℝ) * x^5 * (z - y)^2 + (8/3 : ℝ) * x^4 * (y - x)^3 + (4 : ℝ) * x^4 * (y - x)^2 * (z - y)^1 + (8/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^2 + (2/3 : ℝ) * x^4 * (z - y)^3 + (115/27 : ℝ) * x^3 * (y - x)^4 + (230/27 : ℝ) * x^3 * (y - x)^3 * (z - y)^1 + (55/9 : ℝ) * x^3 * (y - x)^2 * (z - y)^2 + (50/27 : ℝ) * x^3 * (y - x)^1 * (z - y)^3 + (7/27 : ℝ) * x^3 * (z - y)^4 + (262/81 : ℝ) * x^2 * (y - x)^5 + (655/81 : ℝ) * x^2 * (y - x)^4 * (z - y)^1 + (604/81 : ℝ) * x^2 * (y - x)^3 * (z - y)^2 + (251/81 : ℝ) * x^2 * (y - x)^2 * (z - y)^3 + (74/81 : ℝ) * x^2 * (y - x)^1 * (z - y)^4 + (17/81 : ℝ) * x^2 * (z - y)^5 + (259/243 : ℝ) * x^1 * (y - x)^6 + (259/81 : ℝ) * x^1 * (y - x)^5 * (z - y)^1 + (35/9 : ℝ) * x^1 * (y - x)^4 * (z - y)^2 + (595/243 : ℝ) * x^1 * (y - x)^3 * (z - y)^3 + (83/81 : ℝ) * x^1 * (y - x)^2 * (z - y)^4 + (1/3 : ℝ) * x^1 * (y - x)^1 * (z - y)^5 + (10/243 : ℝ) * x^1 * (z - y)^6 + (64/729 : ℝ) * (y - x)^7 + (224/729 : ℝ) * (y - x)^6 * (z - y)^1 + (128/243 : ℝ) * (y - x)^5 * (z - y)^2 + (400/729 : ℝ) * (y - x)^4 * (z - y)^3 + (260/729 : ℝ) * (y - x)^3 * (z - y)^4 + (34/243 : ℝ) * (y - x)^2 * (z - y)^5 + (22/729 : ℝ) * (y - x)^1 * (z - y)^6 + (2/729 : ℝ) * (z - y)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^7/729 + 8*x^6*y/729 + 8*x^6*z/729 + 4*x^5*y^2/243 - x^5*y*z/81 + 4*x^5*z^2/243 + 10*x^4*y^3/729 - 4*x^4*y^2*z/27 - 4*x^4*y*z^2/27 + 10*x^4*z^3/729 + 10*x^3*y^4/729 + 547*x^3*y^3*z/729 - 128*x^3*y^2*z^2/243 + 547*x^3*y*z^3/729 + 10*x^3*z^4/729 + 4*x^2*y^5/243 - 4*x^2*y^4*z/27 - 128*x^2*y^3*z^2/243 - 128*x^2*y^2*z^3/243 - 4*x^2*y*z^4/27 + 4*x^2*z^5/243 + 8*x*y^6/729 - x*y^5*z/81 - 4*x*y^4*z^2/27 + 547*x*y^3*z^3/729 - 4*x*y^2*z^4/27 - x*y*z^5/81 + 8*x*z^6/729 + 2*y^7/729 + 8*y^6*z/729 + 4*y^5*z^2/243 + 10*y^4*z^3/729 + 10*y^3*z^4/729 + 4*y^2*z^5/243 + 8*y*z^6/729 + 2*z^7/729) := by
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
  have he : (x^3*y^3*z + x^3*y*z^3 - x^2*y*z + x*y^3*z^3 - x*y^2*z - x*y*z^2 - 2*x*y - 2*x*z + 2*x - 2*y*z + 2*y + 2*z) = (2*x^7/729 + 8*x^6*y/729 + 8*x^6*z/729 + 4*x^5*y^2/243 - x^5*y*z/81 + 4*x^5*z^2/243 + 10*x^4*y^3/729 - 4*x^4*y^2*z/27 - 4*x^4*y*z^2/27 + 10*x^4*z^3/729 + 10*x^3*y^4/729 + 547*x^3*y^3*z/729 - 128*x^3*y^2*z^2/243 + 547*x^3*y*z^3/729 + 10*x^3*z^4/729 + 4*x^2*y^5/243 - 4*x^2*y^4*z/27 - 128*x^2*y^3*z^2/243 - 128*x^2*y^2*z^3/243 - 4*x^2*y*z^4/27 + 4*x^2*z^5/243 + 8*x*y^6/729 - x*y^5*z/81 - 4*x*y^4*z^2/27 + 547*x*y^3*z^3/729 - 4*x*y^2*z^4/27 - x*y*z^5/81 + 8*x*z^6/729 + 2*y^7/729 + 8*y^6*z/729 + 4*y^5*z^2/243 + 10*y^4*z^3/729 + 10*y^3*z^4/729 + 4*y^2*z^5/243 + 8*y*z^6/729 + 2*z^7/729) := by
    linear_combination (-2*x^6/729 - 2*x^5*y/243 - 2*x^5*z/243 - 2*x^5/243 - 2*x^4*y^2/243 + 7*x^4*y*z/243 - 4*x^4*y/243 - 2*x^4*z^2/243 - 4*x^4*z/243 - 2*x^4/81 - 4*x^3*y^3/729 + 31*x^3*y^2*z/243 - 2*x^3*y^2/243 + 31*x^3*y*z^2/243 + 29*x^3*y*z/243 - 2*x^3*y/81 - 4*x^3*z^3/729 - 2*x^3*z^2/243 - 2*x^3*z/81 - 2*x^3/27 - 2*x^2*y^4/243 + 31*x^2*y^3*z/243 - 2*x^2*y^3/243 + 22*x^2*y^2*z^2/81 + 22*x^2*y^2*z/81 + 31*x^2*y*z^3/243 + 22*x^2*y*z^2/81 + 11*x^2*y*z/27 - 2*x^2*z^4/243 - 2*x^2*z^3/243 - 2*x^2/9 - 2*x*y^5/243 + 7*x*y^4*z/243 - 4*x*y^4/243 + 31*x*y^3*z^2/243 + 29*x*y^3*z/243 - 2*x*y^3/81 + 31*x*y^2*z^3/243 + 22*x*y^2*z^2/81 + 11*x*y^2*z/27 + 7*x*y*z^4/243 + 29*x*y*z^3/243 + 11*x*y*z^2/27 + 2*x*y*z/9 + 2*x*y/9 - 2*x*z^5/243 - 4*x*z^4/243 - 2*x*z^3/81 + 2*x*z/9 - 2*x/3 - 2*y^6/729 - 2*y^5*z/243 - 2*y^5/243 - 2*y^4*z^2/243 - 4*y^4*z/243 - 2*y^4/81 - 4*y^3*z^3/729 - 2*y^3*z^2/243 - 2*y^3*z/81 - 2*y^3/27 - 2*y^2*z^4/243 - 2*y^2*z^3/243 - 2*y^2/9 - 2*y*z^5/243 - 4*y*z^4/243 - 2*y*z^3/81 + 2*y*z/9 - 2*y/3 - 2*z^6/729 - 2*z^5/243 - 2*z^4/81 - 2*z^3/27 - 2*z^2/9 - 2*z/3) * h
  have hn : 0 ≤ (x^3*y^3*z + x^3*y*z^3 - x^2*y*z + x*y^3*z^3 - x*y^2*z - x*y*z^2 - 2*x*y - 2*x*z + 2*x - 2*y*z + 2*y + 2*z) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), (y^3 * z^3 + 2) / (y * z) + (z^3 * x^3 + 2) / (z * x) + (x^3 * y^3 + 2) / (x * y) ≥ (x^2 + 2) / x + (y^2 + 2) / y + (z^2 + 2) / z) := @solution
#print axioms solution
