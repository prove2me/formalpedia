-- Prove2me | solution 1 for WorkbookSource.base_33810
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:38:41.87461+00:00
-- url     : https://prove2.me/submissions/a6105c6e-01eb-462d-86ad-9d528aeaacbc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3) * (x^5 + y^5 + z^5) / (x^8 + y^8 + z^8) ≤ 3  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (2*x^8 - x^5*y^3 - x^5*z^3 - x^3*y^5 - x^3*z^5 + 2*y^8 - y^5*z^3 - y^3*z^5 + 2*z^8) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (30 : ℝ) * x^6 * (y - x)^2 + (30 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (30 : ℝ) * x^6 * (z - y)^2 + (90 : ℝ) * x^5 * (y - x)^3 + (135 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (225 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (90 : ℝ) * x^5 * (z - y)^3 + (130 : ℝ) * x^4 * (y - x)^4 + (260 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (615 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (485 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (130 : ℝ) * x^4 * (z - y)^4 + (110 : ℝ) * x^3 * (y - x)^5 + (275 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (850 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (1000 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (535 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (110 : ℝ) * x^3 * (z - y)^5 + (56 : ℝ) * x^2 * (y - x)^6 + (168 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (645 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (1010 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (810 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (333 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (56 : ℝ) * x^2 * (z - y)^6 + (16 : ℝ) * x^1 * (y - x)^7 + (56 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (258 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (505 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (540 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (333 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (112 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (16 : ℝ) * x^1 * (z - y)^7 + (2 : ℝ) * (y - x)^8 + (8 : ℝ) * (y - x)^7 * (z - y)^1 + (43 : ℝ) * (y - x)^6 * (z - y)^2 + (101 : ℝ) * (y - x)^5 * (z - y)^3 + (135 : ℝ) * (y - x)^4 * (z - y)^4 + (111 : ℝ) * (y - x)^3 * (z - y)^5 + (56 : ℝ) * (y - x)^2 * (z - y)^6 + (16 : ℝ) * (y - x)^1 * (z - y)^7 + (2 : ℝ) * (z - y)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*x^8 - x^5*y^3 - x^5*z^3 - x^3*y^5 - x^3*z^5 + 2*y^8 - y^5*z^3 - y^3*z^5 + 2*z^8) := by
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
  have hn : 0 ≤ (2*x^8 - x^5*y^3 - x^5*z^3 - x^3*y^5 - x^3*z^5 + 2*y^8 - y^5*z^3 - y^3*z^5 + 2*z^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^3 + y^3 + z^3) * (x^5 + y^5 + z^5) / (x^8 + y^8 + z^8) ≤ 3) := @solution
#print axioms solution
