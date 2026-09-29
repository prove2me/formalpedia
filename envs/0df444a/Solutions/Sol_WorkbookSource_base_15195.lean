-- Prove2me | solution 1 for WorkbookSource.base_15195
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:25.182788+00:00
-- url     : https://prove2.me/submissions/de6eea13-8000-4866-b0cc-ab7d24636dbc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 2) : (x^2 + x*y + y^2)*(y^2 + y*z + z^2)*(z^2 + z*x + x^2) ≤ 3  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^6/64 + 9*x^5*y/32 + 9*x^5*z/32 - 19*x^4*y^2/64 + 13*x^4*y*z/32 - 19*x^4*z^2/64 - x^3*y^3/16 + 13*x^3*y^2*z/16 + 13*x^3*y*z^2/16 - x^3*z^3/16 - 19*x^2*y^4/64 + 13*x^2*y^3*z/16 + 39*x^2*y^2*z^2/32 + 13*x^2*y*z^3/16 - 19*x^2*z^4/64 + 9*x*y^5/32 + 13*x*y^4*z/32 + 13*x*y^3*z^2/16 + 13*x*y^2*z^3/16 + 13*x*y*z^4/32 + 9*x*z^5/32 + 3*y^6/64 + 9*y^5*z/32 - 19*y^4*z^2/64 - y^3*z^3/16 - 19*y^2*z^4/64 + 9*y*z^5/32 + 3*z^6/64) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (459/64 : ℝ) * x^6 + (459/16 : ℝ) * x^5 * (y - x)^1 + (459/32 : ℝ) * x^5 * (z - y)^1 + (765/16 : ℝ) * x^4 * (y - x)^2 + (765/16 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (765/64 : ℝ) * x^4 * (z - y)^2 + (81/2 : ℝ) * x^3 * (y - x)^3 + (243/4 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (279/8 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (117/16 : ℝ) * x^3 * (z - y)^3 + (69/4 : ℝ) * x^2 * (y - x)^4 + (69/2 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (279/8 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (141/8 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (213/64 : ℝ) * x^2 * (z - y)^4 + (3 : ℝ) * x^1 * (y - x)^5 + (15/2 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (27/2 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (51/4 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (87/16 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (27/32 : ℝ) * x^1 * (z - y)^5 + (5/4 : ℝ) * (y - x)^4 * (z - y)^2 + (5/2 : ℝ) * (y - x)^3 * (z - y)^3 + (29/16 : ℝ) * (y - x)^2 * (z - y)^4 + (9/16 : ℝ) * (y - x)^1 * (z - y)^5 + (3/64 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^6/64 + 9*x^5*y/32 + 9*x^5*z/32 - 19*x^4*y^2/64 + 13*x^4*y*z/32 - 19*x^4*z^2/64 - x^3*y^3/16 + 13*x^3*y^2*z/16 + 13*x^3*y*z^2/16 - x^3*z^3/16 - 19*x^2*y^4/64 + 13*x^2*y^3*z/16 + 39*x^2*y^2*z^2/32 + 13*x^2*y*z^3/16 - 19*x^2*z^4/64 + 9*x*y^5/32 + 13*x*y^4*z/32 + 13*x*y^3*z^2/16 + 13*x*y^2*z^3/16 + 13*x*y*z^4/32 + 9*x*z^5/32 + 3*y^6/64 + 9*y^5*z/32 - 19*y^4*z^2/64 - y^3*z^3/16 - 19*y^2*z^4/64 + 9*y*z^5/32 + 3*z^6/64) := by
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
  have he : (-x^4*y^2 - x^4*y*z - x^4*z^2 - x^3*y^3 - 2*x^3*y^2*z - 2*x^3*y*z^2 - x^3*z^3 - x^2*y^4 - 2*x^2*y^3*z - 3*x^2*y^2*z^2 - 2*x^2*y*z^3 - x^2*z^4 - x*y^4*z - 2*x*y^3*z^2 - 2*x*y^2*z^3 - x*y*z^4 - y^4*z^2 - y^3*z^3 - y^2*z^4 + 3) = (3*x^6/64 + 9*x^5*y/32 + 9*x^5*z/32 - 19*x^4*y^2/64 + 13*x^4*y*z/32 - 19*x^4*z^2/64 - x^3*y^3/16 + 13*x^3*y^2*z/16 + 13*x^3*y*z^2/16 - x^3*z^3/16 - 19*x^2*y^4/64 + 13*x^2*y^3*z/16 + 39*x^2*y^2*z^2/32 + 13*x^2*y*z^3/16 - 19*x^2*z^4/64 + 9*x*y^5/32 + 13*x*y^4*z/32 + 13*x*y^3*z^2/16 + 13*x*y^2*z^3/16 + 13*x*y*z^4/32 + 9*x*z^5/32 + 3*y^6/64 + 9*y^5*z/32 - 19*y^4*z^2/64 - y^3*z^3/16 - 19*y^2*z^4/64 + 9*y*z^5/32 + 3*z^6/64) := by
    linear_combination (-3*x^5/64 - 15*x^4*y/64 - 15*x^4*z/64 - 3*x^4/32 - 15*x^3*y^2/32 - 15*x^3*y*z/16 - 3*x^3*y/8 - 15*x^3*z^2/32 - 3*x^3*z/8 - 3*x^3/16 - 15*x^2*y^3/32 - 45*x^2*y^2*z/32 - 9*x^2*y^2/16 - 45*x^2*y*z^2/32 - 9*x^2*y*z/8 - 9*x^2*y/16 - 15*x^2*z^3/32 - 9*x^2*z^2/16 - 9*x^2*z/16 - 3*x^2/8 - 15*x*y^4/64 - 15*x*y^3*z/16 - 3*x*y^3/8 - 45*x*y^2*z^2/32 - 9*x*y^2*z/8 - 9*x*y^2/16 - 15*x*y*z^3/16 - 9*x*y*z^2/8 - 9*x*y*z/8 - 3*x*y/4 - 15*x*z^4/64 - 3*x*z^3/8 - 9*x*z^2/16 - 3*x*z/4 - 3*x/4 - 3*y^5/64 - 15*y^4*z/64 - 3*y^4/32 - 15*y^3*z^2/32 - 3*y^3*z/8 - 3*y^3/16 - 15*y^2*z^3/32 - 9*y^2*z^2/16 - 9*y^2*z/16 - 3*y^2/8 - 15*y*z^4/64 - 3*y*z^3/8 - 9*y*z^2/16 - 3*y*z/4 - 3*y/4 - 3*z^5/64 - 3*z^4/32 - 3*z^3/16 - 3*z^2/8 - 3*z/4 - 3/2) * h
  nlinarith only [hp, he]
example : (∀ (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 2), (x^2 + x*y + y^2)*(y^2 + y*z + z^2)*(z^2 + z*x + x^2) ≤ 3) := @solution
#print axioms solution
