-- Prove2me | solution 1 for WorkbookSource.base_39820
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:36.862884+00:00
-- url     : https://prove2.me/submissions/8e256ddd-e003-4ab8-90d2-8b4cf9eba31d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hx2 : x^2 ≤ y^2 + z^2) (hy2 : y^2 ≤ z^2 + x^2) (hz2 : z^2 ≤ x^2 + y^2) :  x^8 + y^8 + z^8 + x^6 * y * z + x * y^6 * z + x * y * z^6 + 2 * x^3 * y^3 * z^2 + 2 * x^3 * y^2 * z^3 + 2 * x^2 * y^3 * z^3 ≥ x^5 * y^2 * z + y^5 * z^2 * x + z^5 * x^2 * y + x^5 * y * z^2 + y^5 * z * x^2 + z^5 * x * y^2 + 2 * x^4 * y^4 + 2 * y^4 * z^4 + 2 * z^4 * x^4  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (x^8 + x^6*y*z - x^5*y^2*z - x^5*y*z^2 - 2*x^4*y^4 - 2*x^4*z^4 + 2*x^3*y^3*z^2 + 2*x^3*y^2*z^3 - x^2*y^5*z + 2*x^2*y^3*z^3 - x^2*y*z^5 + x*y^6*z - x*y^5*z^2 - x*y^2*z^5 + x*y*z^6 + y^8 - 2*y^4*z^4 + z^8) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * x^6 * (y - x)^2 + (11 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (11 : ℝ) * x^6 * (z - y)^2 + (22 : ℝ) * x^5 * (y - x)^3 + (33 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (99 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (44 : ℝ) * x^5 * (z - y)^3 + (16 : ℝ) * x^4 * (y - x)^4 + (32 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (268 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (252 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (71 : ℝ) * x^4 * (z - y)^4 + (4 : ℝ) * x^3 * (y - x)^5 + (10 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (352 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (518 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (292 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (60 : ℝ) * x^3 * (z - y)^5 + (256 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (512 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (433 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (177 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (29 : ℝ) * x^2 * (z - y)^6 + (100 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (250 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (282 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (173 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (57 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (8 : ℝ) * x^1 * (z - y)^7 + (16 : ℝ) * (y - x)^6 * (z - y)^2 + (48 : ℝ) * (y - x)^5 * (z - y)^3 + (68 : ℝ) * (y - x)^4 * (z - y)^4 + (56 : ℝ) * (y - x)^3 * (z - y)^5 + (28 : ℝ) * (y - x)^2 * (z - y)^6 + (8 : ℝ) * (y - x)^1 * (z - y)^7 + (1 : ℝ) * (z - y)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (x^8 + x^6*y*z - x^5*y^2*z - x^5*y*z^2 - 2*x^4*y^4 - 2*x^4*z^4 + 2*x^3*y^3*z^2 + 2*x^3*y^2*z^3 - x^2*y^5*z + 2*x^2*y^3*z^3 - x^2*y*z^5 + x*y^6*z - x*y^5*z^2 - x*y^2*z^5 + x*y*z^6 + y^8 - 2*y^4*z^4 + z^8) := by
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
example : (∀ {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hx2 : x^2 ≤ y^2 + z^2) (hy2 : y^2 ≤ z^2 + x^2) (hz2 : z^2 ≤ x^2 + y^2), x^8 + y^8 + z^8 + x^6 * y * z + x * y^6 * z + x * y * z^6 + 2 * x^3 * y^3 * z^2 + 2 * x^3 * y^2 * z^3 + 2 * x^2 * y^3 * z^3 ≥ x^5 * y^2 * z + y^5 * z^2 * x + z^5 * x^2 * y + x^5 * y * z^2 + y^5 * z * x^2 + z^5 * x * y^2 + 2 * x^4 * y^4 + 2 * y^4 * z^4 + 2 * z^4 * x^4) := @solution
#print axioms solution
