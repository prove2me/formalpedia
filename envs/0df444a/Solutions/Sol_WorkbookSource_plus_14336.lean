-- Prove2me | solution 1 for WorkbookSource.plus_14336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:16:54.8344+00:00
-- url     : https://prove2.me/submissions/3229eb54-e59a-4ac0-b22f-e6108fb80db9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (64 / 3) * (x * y + y * z + z * x) ≤ 55 + 9 * (x * y * z) ^ 2   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (55*x^6/243 + 46*x^5*y/81 + 46*x^5*z/81 + 19*x^4*y^2/81 - 26*x^4*y*z/81 + 19*x^4*z^2/81 - 52*x^3*y^3/243 - 308*x^3*y^2*z/81 - 308*x^3*y*z^2/81 - 52*x^3*z^3/243 + 19*x^2*y^4/81 - 308*x^2*y^3*z/81 + 511*x^2*y^2*z^2/27 - 308*x^2*y*z^3/81 + 19*x^2*z^4/81 + 46*x*y^5/81 - 26*x*y^4*z/81 - 308*x*y^3*z^2/81 - 308*x*y^2*z^3/81 - 26*x*y*z^4/81 + 46*x*z^5/81 + 55*y^6/243 + 46*y^5*z/81 + 19*y^4*z^2/81 - 52*y^3*z^3/243 + 19*y^2*z^4/81 + 46*y*z^5/81 + 55*z^6/243) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (10/3 : ℝ) * x^4 * (y - x)^2 + (10/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (10/3 : ℝ) * x^4 * (z - y)^2 + (44/9 : ℝ) * x^3 * (y - x)^3 + (22/3 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (58/3 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (76/9 : ℝ) * x^3 * (z - y)^3 + (35/9 : ℝ) * x^2 * (y - x)^4 + (70/9 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (35 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (280/9 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (83/9 : ℝ) * x^2 * (z - y)^4 + (320/81 : ℝ) * x^1 * (y - x)^5 + (800/81 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (2336/81 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (2704/81 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (1252/81 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (202/81 : ℝ) * x^1 * (z - y)^5 + (448/243 : ℝ) * (y - x)^6 + (448/81 : ℝ) * (y - x)^5 * (z - y)^1 + (272/27 : ℝ) * (y - x)^4 * (z - y)^2 + (2656/243 : ℝ) * (y - x)^3 * (z - y)^3 + (524/81 : ℝ) * (y - x)^2 * (z - y)^4 + (52/27 : ℝ) * (y - x)^1 * (z - y)^5 + (55/243 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (55*x^6/243 + 46*x^5*y/81 + 46*x^5*z/81 + 19*x^4*y^2/81 - 26*x^4*y*z/81 + 19*x^4*z^2/81 - 52*x^3*y^3/243 - 308*x^3*y^2*z/81 - 308*x^3*y*z^2/81 - 52*x^3*z^3/243 + 19*x^2*y^4/81 - 308*x^2*y^3*z/81 + 511*x^2*y^2*z^2/27 - 308*x^2*y*z^3/81 + 19*x^2*z^4/81 + 46*x*y^5/81 - 26*x*y^4*z/81 - 308*x*y^3*z^2/81 - 308*x*y^2*z^3/81 - 26*x*y*z^4/81 + 46*x*z^5/81 + 55*y^6/243 + 46*y^5*z/81 + 19*y^4*z^2/81 - 52*y^3*z^3/243 + 19*y^2*z^4/81 + 46*y*z^5/81 + 55*z^6/243) := by
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
  have he : (27*x^2*y^2*z^2 - 64*x*y - 64*x*z - 64*y*z + 165) = (55*x^6/243 + 46*x^5*y/81 + 46*x^5*z/81 + 19*x^4*y^2/81 - 26*x^4*y*z/81 + 19*x^4*z^2/81 - 52*x^3*y^3/243 - 308*x^3*y^2*z/81 - 308*x^3*y*z^2/81 - 52*x^3*z^3/243 + 19*x^2*y^4/81 - 308*x^2*y^3*z/81 + 511*x^2*y^2*z^2/27 - 308*x^2*y*z^3/81 + 19*x^2*z^4/81 + 46*x*y^5/81 - 26*x*y^4*z/81 - 308*x*y^3*z^2/81 - 308*x*y^2*z^3/81 - 26*x*y*z^4/81 + 46*x*z^5/81 + 55*y^6/243 + 46*y^5*z/81 + 19*y^4*z^2/81 - 52*y^3*z^3/243 + 19*y^2*z^4/81 + 46*y*z^5/81 + 55*z^6/243) := by
    linear_combination (-55*x^5/243 - 83*x^4*y/243 - 83*x^4*z/243 - 55*x^4/81 + 26*x^3*y^2/243 + 244*x^3*y*z/243 - 28*x^3*y/81 + 26*x^3*z^2/243 - 28*x^3*z/81 - 55*x^3/27 + 26*x^2*y^3/243 + 218*x^2*y^2*z/81 + 2*x^2*y^2/3 + 218*x^2*y*z^2/81 + 100*x^2*y*z/27 + x^2*y + 26*x^2*z^3/243 + 2*x^2*z^2/3 + x^2*z - 55*x^2/9 - 83*x*y^4/243 + 244*x*y^3*z/243 - 28*x*y^3/81 + 218*x*y^2*z^2/81 + 100*x*y^2*z/27 + x*y^2 + 244*x*y*z^3/243 + 100*x*y*z^2/27 + 82*x*y*z/9 + 82*x*y/9 - 83*x*z^4/243 - 28*x*z^3/81 + x*z^2 + 82*x*z/9 - 55*x/3 - 55*y^5/243 - 83*y^4*z/243 - 55*y^4/81 + 26*y^3*z^2/243 - 28*y^3*z/81 - 55*y^3/27 + 26*y^2*z^3/243 + 2*y^2*z^2/3 + y^2*z - 55*y^2/9 - 83*y*z^4/243 - 28*y*z^3/81 + y*z^2 + 82*y*z/9 - 55*y/3 - 55*z^5/243 - 55*z^4/81 - 55*z^3/27 - 55*z^2/9 - 55*z/3 - 55) * h
  have hn : 0 ≤ (27*x^2*y^2*z^2 - 64*x*y - 64*x*z - 64*y*z + 165) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), (64 / 3) * (x * y + y * z + z * x) ≤ 55 + 9 * (x * y * z) ^ 2) := @solution
#print axioms solution
