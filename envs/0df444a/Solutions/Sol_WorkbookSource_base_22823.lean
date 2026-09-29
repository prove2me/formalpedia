-- Prove2me | solution 1 for WorkbookSource.base_22823
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:28.540275+00:00
-- url     : https://prove2.me/submissions/2ba1d0bb-232d-4ec7-bc5f-accba7efe20c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) ^ 6 ≥ 64 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y)  := by
  have haux (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^6 + 6*x^5*y + 6*x^5*z + 15*x^4*y^2 - 34*x^4*y*z + 15*x^4*z^2 - 44*x^3*y^3 + 60*x^3*y^2*z + 60*x^3*y*z^2 - 44*x^3*z^3 + 15*x^2*y^4 + 60*x^2*y^3*z - 38*x^2*y^2*z^2 + 60*x^2*y*z^3 + 15*x^2*z^4 + 6*x*y^5 - 34*x*y^4*z + 60*x*y^3*z^2 + 60*x*y^2*z^3 - 34*x*y*z^4 + 6*x*z^5 + y^6 + 6*y^5*z + 15*y^4*z^2 - 44*y^3*z^3 + 15*y^2*z^4 + 6*y*z^5 + z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (217 : ℝ) * x^6 + (868 : ℝ) * x^5 * (y - x)^1 + (434 : ℝ) * x^5 * (z - y)^1 + (1404 : ℝ) * x^4 * (y - x)^2 + (1404 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (319 : ℝ) * x^4 * (z - y)^2 + (1120 : ℝ) * x^3 * (y - x)^3 + (1680 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (872 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (156 : ℝ) * x^3 * (z - y)^3 + (432 : ℝ) * x^2 * (y - x)^4 + (864 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (808 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (376 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (71 : ℝ) * x^2 * (z - y)^4 + (64 : ℝ) * x^1 * (y - x)^5 + (160 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (288 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (272 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (116 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (18 : ℝ) * x^1 * (z - y)^5 + (48 : ℝ) * (y - x)^4 * (z - y)^2 + (96 : ℝ) * (y - x)^3 * (z - y)^3 + (60 : ℝ) * (y - x)^2 * (z - y)^4 + (12 : ℝ) * (y - x)^1 * (z - y)^5 + (1 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^6 + 6*x^5*y + 6*x^5*z + 15*x^4*y^2 - 34*x^4*y*z + 15*x^4*z^2 - 44*x^3*y^3 + 60*x^3*y^2*z + 60*x^3*y*z^2 - 44*x^3*z^3 + 15*x^2*y^4 + 60*x^2*y^3*z - 38*x^2*y^2*z^2 + 60*x^2*y*z^3 + 15*x^2*z^4 + 6*x*y^5 - 34*x*y^4*z + 60*x*y^3*z^2 + 60*x*y^2*z^3 - 34*x*y*z^4 + 6*x*z^5 + y^6 + 6*y^5*z + 15*y^4*z^2 - 44*y^3*z^3 + 15*y^2*z^4 + 6*y*z^5 + z^6) := by
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
  nlinarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), (x + y + z) ^ 6 ≥ 64 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y)) := @solution
#print axioms solution
