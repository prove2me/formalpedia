-- Prove2me | solution 1 for WorkbookSource.plus_73339
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:37.783445+00:00
-- url     : https://prove2.me/submissions/03fa9c7f-d7ba-4cb6-8cc8-f34ba0602e71

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) ^ 8 ≥ 243 * (x * y + x * z + y * z) ^ 2 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2)   := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^8 + 8*x^7*y + 8*x^7*z + 28*x^6*y^2 + 56*x^6*y*z + 28*x^6*z^2 + 56*x^5*y^3 + 168*x^5*y^2*z + 168*x^5*y*z^2 + 56*x^5*z^3 - 173*x^4*y^4 - 206*x^4*y^3*z - 66*x^4*y^2*z^2 - 206*x^4*y*z^3 - 173*x^4*z^4 + 56*x^3*y^5 - 206*x^3*y^4*z + 74*x^3*y^3*z^2 + 74*x^3*y^2*z^3 - 206*x^3*y*z^4 + 56*x^3*z^5 + 28*x^2*y^6 + 168*x^2*y^5*z - 66*x^2*y^4*z^2 + 74*x^2*y^3*z^3 - 66*x^2*y^2*z^4 + 168*x^2*y*z^5 + 28*x^2*z^6 + 8*x*y^7 + 56*x*y^6*z + 168*x*y^5*z^2 - 206*x*y^4*z^3 - 206*x*y^3*z^4 + 168*x*y^2*z^5 + 56*x*y*z^6 + 8*x*z^7 + y^8 + 8*y^7*z + 28*y^6*z^2 + 56*y^5*z^3 - 173*y^4*z^4 + 56*y^3*z^5 + 28*y^2*z^6 + 8*y*z^7 + z^8) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (1458 : ℝ) * x^6 * (y - x)^2 + (1458 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (1458 : ℝ) * x^6 * (z - y)^2 + (4860 : ℝ) * x^5 * (y - x)^3 + (7290 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (10206 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (3888 : ℝ) * x^5 * (z - y)^3 + (6156 : ℝ) * x^4 * (y - x)^4 + (12312 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (23328 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (17172 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (3726 : ℝ) * x^4 * (z - y)^4 + (3672 : ℝ) * x^3 * (y - x)^5 + (9180 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (23760 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (26460 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (11232 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (1512 : ℝ) * x^3 * (z - y)^5 + (1062 : ℝ) * x^2 * (y - x)^6 + (3186 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (11880 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (18450 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (11718 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (3024 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (252 : ℝ) * x^2 * (z - y)^6 + (156 : ℝ) * x^1 * (y - x)^7 + (546 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (3006 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (6150 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (5262 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (2016 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (336 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (24 : ℝ) * x^1 * (z - y)^7 + (13 : ℝ) * (y - x)^8 + (52 : ℝ) * (y - x)^7 * (z - y)^1 + (334 : ℝ) * (y - x)^6 * (z - y)^2 + (820 : ℝ) * (y - x)^5 * (z - y)^3 + (877 : ℝ) * (y - x)^4 * (z - y)^4 + (448 : ℝ) * (y - x)^3 * (z - y)^5 + (112 : ℝ) * (y - x)^2 * (z - y)^6 + (16 : ℝ) * (y - x)^1 * (z - y)^7 + (1 : ℝ) * (z - y)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^8 + 8*x^7*y + 8*x^7*z + 28*x^6*y^2 + 56*x^6*y*z + 28*x^6*z^2 + 56*x^5*y^3 + 168*x^5*y^2*z + 168*x^5*y*z^2 + 56*x^5*z^3 - 173*x^4*y^4 - 206*x^4*y^3*z - 66*x^4*y^2*z^2 - 206*x^4*y*z^3 - 173*x^4*z^4 + 56*x^3*y^5 - 206*x^3*y^4*z + 74*x^3*y^3*z^2 + 74*x^3*y^2*z^3 - 206*x^3*y*z^4 + 56*x^3*z^5 + 28*x^2*y^6 + 168*x^2*y^5*z - 66*x^2*y^4*z^2 + 74*x^2*y^3*z^3 - 66*x^2*y^2*z^4 + 168*x^2*y*z^5 + 28*x^2*z^6 + 8*x*y^7 + 56*x*y^6*z + 168*x*y^5*z^2 - 206*x*y^4*z^3 - 206*x*y^3*z^4 + 168*x*y^2*z^5 + 56*x*y*z^6 + 8*x*z^7 + y^8 + 8*y^7*z + 28*y^6*z^2 + 56*y^5*z^3 - 173*y^4*z^4 + 56*y^3*z^5 + 28*y^2*z^6 + 8*y*z^7 + z^8) := by
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
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), (x + y + z) ^ 8 ≥ 243 * (x * y + x * z + y * z) ^ 2 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2)) := @solution
#print axioms solution
