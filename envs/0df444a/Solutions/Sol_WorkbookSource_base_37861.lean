-- Prove2me | solution 1 for WorkbookSource.base_37861
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:39:47.313783+00:00
-- url     : https://prove2.me/submissions/7f37ab20-de36-43ce-86f1-7f3dc971f4d9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * (3 * x - y) / (y * (3 * z + x)) + y * (3 * y - z) / (z * (3 * x + y)) + z * (3 * z - x) / (x * (3 * y + z))) ≥ 3 / 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (54*x^4*y*z + 18*x^4*z^2 - 27*x^3*y^2*z - 15*x^3*y*z^2 + 18*x^2*y^4 - 15*x^2*y^3*z - 90*x^2*y^2*z^2 - 27*x^2*y*z^3 + 54*x*y^4*z - 27*x*y^3*z^2 - 15*x*y^2*z^3 + 54*x*y*z^4 + 18*y^2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (192 : ℝ) * x^4 * (y - x)^2 + (192 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (192 : ℝ) * x^4 * (z - y)^2 + (522 : ℝ) * x^3 * (y - x)^3 + (861 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (831 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (246 : ℝ) * x^3 * (z - y)^3 + (486 : ℝ) * x^2 * (y - x)^4 + (1128 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (1233 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (591 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (72 : ℝ) * x^2 * (z - y)^4 + (174 : ℝ) * x^1 * (y - x)^5 + (531 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (684 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (417 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (90 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (18 : ℝ) * (y - x)^6 + (72 : ℝ) * (y - x)^5 * (z - y)^1 + (108 : ℝ) * (y - x)^4 * (z - y)^2 + (72 : ℝ) * (y - x)^3 * (z - y)^3 + (18 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (54*x^4*y*z + 18*x^4*z^2 - 27*x^3*y^2*z - 15*x^3*y*z^2 + 18*x^2*y^4 - 15*x^2*y^3*z - 90*x^2*y^2*z^2 - 27*x^2*y*z^3 + 54*x*y^4*z - 27*x*y^3*z^2 - 15*x*y^2*z^3 + 54*x*y*z^4 + 18*y^2*z^4) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (192 : ℝ) * x^4 * (z - x)^2 + (192 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (192 : ℝ) * x^4 * (y - z)^2 + (522 : ℝ) * x^3 * (z - x)^3 + (705 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (675 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (246 : ℝ) * x^3 * (y - z)^3 + (486 : ℝ) * x^2 * (z - x)^4 + (816 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (765 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (435 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (72 : ℝ) * x^2 * (y - z)^4 + (174 : ℝ) * x^1 * (z - x)^5 + (339 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (300 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (189 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (54 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (18 : ℝ) * (z - x)^6 + (36 : ℝ) * (z - x)^5 * (y - z)^1 + (18 : ℝ) * (z - x)^4 * (y - z)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (54*x^4*y*z + 18*x^4*z^2 - 27*x^3*y^2*z - 15*x^3*y*z^2 + 18*x^2*y^4 - 15*x^2*y^3*z - 90*x^2*y^2*z^2 - 27*x^2*y*z^3 + 54*x*y^4*z - 27*x*y^3*z^2 - 15*x*y^2*z^3 + 54*x*y*z^4 + 18*y^2*z^4) := by
    rcases le_total x y with hab | hba
    · rcases le_total y z with hbc | hcb
      ·
        convert haux0 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total x z with hac | hca
        ·
          convert haux1 x y z (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total x z with hbc | hcb
      ·
        convert haux1 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total y z with hac | hca
        ·
          convert haux0 y z x (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 z x y (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (54*x^4*y*z + 18*x^4*z^2 - 27*x^3*y^2*z - 15*x^3*y*z^2 + 18*x^2*y^4 - 15*x^2*y^3*z - 90*x^2*y^2*z^2 - 27*x^2*y*z^3 + 54*x*y^4*z - 27*x*y^3*z^2 - 15*x*y^2*z^3 + 54*x*y*z^4 + 18*y^2*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x * (3 * x - y) / (y * (3 * z + x)) + y * (3 * y - z) / (z * (3 * x + y)) + z * (3 * z - x) / (x * (3 * y + z))) ≥ 3 / 2) := @solution
#print axioms solution
