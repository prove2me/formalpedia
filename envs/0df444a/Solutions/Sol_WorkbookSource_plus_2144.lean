-- Prove2me | solution 1 for WorkbookSource.plus_2144
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:34.459935+00:00
-- url     : https://prove2.me/submissions/31db0140-1673-4c95-892a-e3016d0d21c0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 2) : x^3*y^3 + y^3*z^3 + z^3*x^3 + 2*x*y*z ≤ 1   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6/64 + 3*x^5*y/32 + 3*x^5*z/32 + 15*x^4*y^2/64 + 7*x^4*y*z/32 + 15*x^4*z^2/64 - 11*x^3*y^3/16 + 3*x^3*y^2*z/16 + 3*x^3*y*z^2/16 - 11*x^3*z^3/16 + 15*x^2*y^4/64 + 3*x^2*y^3*z/16 - 3*x^2*y^2*z^2/32 + 3*x^2*y*z^3/16 + 15*x^2*z^4/64 + 3*x*y^5/32 + 7*x*y^4*z/32 + 3*x*y^3*z^2/16 + 3*x*y^2*z^3/16 + 7*x*y*z^4/32 + 3*x*z^5/32 + y^6/64 + 3*y^5*z/32 + 15*y^4*z^2/64 - 11*y^3*z^3/16 + 15*y^2*z^4/64 + 3*y*z^5/32 + z^6/64) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (105/64 : ℝ) * x^6 + (105/16 : ℝ) * x^5 * (y - x)^1 + (105/32 : ℝ) * x^5 * (z - y)^1 + (195/16 : ℝ) * x^4 * (y - x)^2 + (195/16 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (255/64 : ℝ) * x^4 * (z - y)^2 + (12 : ℝ) * x^3 * (y - x)^3 + (18 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (111/8 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (63/16 : ℝ) * x^3 * (z - y)^3 + (23/4 : ℝ) * x^2 * (y - x)^4 + (23/2 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (123/8 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (77/8 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (119/64 : ℝ) * x^2 * (z - y)^4 + (1 : ℝ) * x^1 * (y - x)^5 + (5/2 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (6 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (13/2 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (41/16 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (9/32 : ℝ) * x^1 * (z - y)^5 + (3/4 : ℝ) * (y - x)^4 * (z - y)^2 + (3/2 : ℝ) * (y - x)^3 * (z - y)^3 + (15/16 : ℝ) * (y - x)^2 * (z - y)^4 + (3/16 : ℝ) * (y - x)^1 * (z - y)^5 + (1/64 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6/64 + 3*x^5*y/32 + 3*x^5*z/32 + 15*x^4*y^2/64 + 7*x^4*y*z/32 + 15*x^4*z^2/64 - 11*x^3*y^3/16 + 3*x^3*y^2*z/16 + 3*x^3*y*z^2/16 - 11*x^3*z^3/16 + 15*x^2*y^4/64 + 3*x^2*y^3*z/16 - 3*x^2*y^2*z^2/32 + 3*x^2*y*z^3/16 + 15*x^2*z^4/64 + 3*x*y^5/32 + 7*x*y^4*z/32 + 3*x*y^3*z^2/16 + 3*x*y^2*z^3/16 + 7*x*y*z^4/32 + 3*x*z^5/32 + y^6/64 + 3*y^5*z/32 + 15*y^4*z^2/64 - 11*y^3*z^3/16 + 15*y^2*z^4/64 + 3*y*z^5/32 + z^6/64) := by
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
  have he : (-x^3*y^3 - x^3*z^3 - 2*x*y*z - y^3*z^3 + 1) = (x^6/64 + 3*x^5*y/32 + 3*x^5*z/32 + 15*x^4*y^2/64 + 7*x^4*y*z/32 + 15*x^4*z^2/64 - 11*x^3*y^3/16 + 3*x^3*y^2*z/16 + 3*x^3*y*z^2/16 - 11*x^3*z^3/16 + 15*x^2*y^4/64 + 3*x^2*y^3*z/16 - 3*x^2*y^2*z^2/32 + 3*x^2*y*z^3/16 + 15*x^2*z^4/64 + 3*x*y^5/32 + 7*x*y^4*z/32 + 3*x*y^3*z^2/16 + 3*x*y^2*z^3/16 + 7*x*y*z^4/32 + 3*x*z^5/32 + y^6/64 + 3*y^5*z/32 + 15*y^4*z^2/64 - 11*y^3*z^3/16 + 15*y^2*z^4/64 + 3*y*z^5/32 + z^6/64) := by
    linear_combination (-x^5/64 - 5*x^4*y/64 - 5*x^4*z/64 - x^4/32 - 5*x^3*y^2/32 - x^3*y*z/16 - x^3*y/8 - 5*x^3*z^2/32 - x^3*z/8 - x^3/16 - 5*x^2*y^3/32 + x^2*y^2*z/32 - 3*x^2*y^2/16 + x^2*y*z^2/32 + x^2*y*z/8 - 3*x^2*y/16 - 5*x^2*z^3/32 - 3*x^2*z^2/16 - 3*x^2*z/16 - x^2/8 - 5*x*y^4/64 - x*y^3*z/16 - x*y^3/8 + x*y^2*z^2/32 + x*y^2*z/8 - 3*x*y^2/16 - x*y*z^3/16 + x*y*z^2/8 + 5*x*y*z/8 - x*y/4 - 5*x*z^4/64 - x*z^3/8 - 3*x*z^2/16 - x*z/4 - x/4 - y^5/64 - 5*y^4*z/64 - y^4/32 - 5*y^3*z^2/32 - y^3*z/8 - y^3/16 - 5*y^2*z^3/32 - 3*y^2*z^2/16 - 3*y^2*z/16 - y^2/8 - 5*y*z^4/64 - y*z^3/8 - 3*y*z^2/16 - y*z/4 - y/4 - z^5/64 - z^4/32 - z^3/16 - z^2/8 - z/4 - 1/2) * h
  nlinarith only [hp, he]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 2), x^3*y^3 + y^3*z^3 + z^3*x^3 + 2*x*y*z ≤ 1) := @solution
#print axioms solution
