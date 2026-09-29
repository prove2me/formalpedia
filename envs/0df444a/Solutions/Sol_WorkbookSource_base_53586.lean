-- Prove2me | solution 1 for WorkbookSource.base_53586
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:29.319872+00:00
-- url     : https://prove2.me/submissions/e999f460-ca16-492c-b6ae-e760ae2fd528

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (7*x^2 + (y + z)^2 - x*(y + z))*(7*y^2 + (x + z)^2 - y*(x + z))*(7*z^2 + (x + y)^2 - z*(x + y)) ≥ (x + y + z)^6  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (6*x^6 + 27*x^4*y^2 - 9*x^4*y*z + 27*x^4*z^2 + 66*x^3*y^3 - 108*x^3*y^2*z - 108*x^3*y*z^2 + 66*x^3*z^3 + 27*x^2*y^4 - 108*x^2*y^3*z + 297*x^2*y^2*z^2 - 108*x^2*y*z^3 + 27*x^2*z^4 - 9*x*y^4*z - 108*x*y^3*z^2 - 108*x*y^2*z^3 - 9*x*y*z^4 + 6*y^6 + 27*y^4*z^2 + 66*y^3*z^3 + 27*y^2*z^4 + 6*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (243 : ℝ) * x^4 * (y - x)^2 + (243 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (243 : ℝ) * x^4 * (z - y)^2 + (756 : ℝ) * x^3 * (y - x)^3 + (1134 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (810 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (216 : ℝ) * x^3 * (z - y)^3 + (945 : ℝ) * x^2 * (y - x)^4 + (1890 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (1539 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (594 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (135 : ℝ) * x^2 * (z - y)^4 + (558 : ℝ) * x^1 * (y - x)^5 + (1395 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (1422 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (738 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (225 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (36 : ℝ) * x^1 * (z - y)^5 + (132 : ℝ) * (y - x)^6 + (396 : ℝ) * (y - x)^5 * (z - y)^1 + (477 : ℝ) * (y - x)^4 * (z - y)^2 + (294 : ℝ) * (y - x)^3 * (z - y)^3 + (117 : ℝ) * (y - x)^2 * (z - y)^4 + (36 : ℝ) * (y - x)^1 * (z - y)^5 + (6 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*x^6 + 27*x^4*y^2 - 9*x^4*y*z + 27*x^4*z^2 + 66*x^3*y^3 - 108*x^3*y^2*z - 108*x^3*y*z^2 + 66*x^3*z^3 + 27*x^2*y^4 - 108*x^2*y^3*z + 297*x^2*y^2*z^2 - 108*x^2*y*z^3 + 27*x^2*z^4 - 9*x*y^4*z - 108*x*y^3*z^2 - 108*x*y^2*z^3 - 9*x*y*z^4 + 6*y^6 + 27*y^4*z^2 + 66*y^3*z^3 + 27*y^2*z^4 + 6*z^6) := by
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
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (7*x^2 + (y + z)^2 - x*(y + z))*(7*y^2 + (x + z)^2 - y*(x + z))*(7*z^2 + (x + y)^2 - z*(x + y)) ≥ (x + y + z)^6) := @solution
#print axioms solution
