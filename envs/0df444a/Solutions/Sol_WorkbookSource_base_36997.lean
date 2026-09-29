-- Prove2me | solution 1 for WorkbookSource.base_36997
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:27:00.628395+00:00
-- url     : https://prove2.me/submissions/4ad5a9fa-ddd1-4328-8ae2-e5fde6411d07

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2 * (x^2 - y^2) / (x^2 + 3 * y^2) + y^2 * (y^2 - z^2) / (y^2 + 3 * z^2) + z^2 * (z^2 - x^2) / (z^2 + 3 * x^2) ≥ 0  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (3*x^6*y^2 + 9*x^6*z^2 - 12*x^4*y^2*z^2 + 9*x^2*y^6 - 12*x^2*y^4*z^2 - 12*x^2*y^2*z^4 + 3*x^2*z^6 + 3*y^6*z^2 + 9*y^2*z^6) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * x^6 * (y - x)^2 + (96 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (96 : ℝ) * x^6 * (z - y)^2 + (384 : ℝ) * x^5 * (y - x)^3 + (648 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (648 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (192 : ℝ) * x^5 * (z - y)^3 + (648 : ℝ) * x^4 * (y - x)^4 + (1536 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (1824 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (936 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (168 : ℝ) * x^4 * (z - y)^4 + (600 : ℝ) * x^3 * (y - x)^5 + (1830 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (2604 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (1836 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (606 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (72 : ℝ) * x^3 * (z - y)^5 + (324 : ℝ) * x^2 * (y - x)^6 + (1206 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (2031 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (1812 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (843 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (180 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (12 : ℝ) * x^2 * (z - y)^6 + (96 : ℝ) * x^1 * (y - x)^7 + (420 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (828 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (900 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (540 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (162 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (18 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (12 : ℝ) * (y - x)^8 + (60 : ℝ) * (y - x)^7 * (z - y)^1 + (138 : ℝ) * (y - x)^6 * (z - y)^2 + (180 : ℝ) * (y - x)^5 * (z - y)^3 + (135 : ℝ) * (y - x)^4 * (z - y)^4 + (54 : ℝ) * (y - x)^3 * (z - y)^5 + (9 : ℝ) * (y - x)^2 * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (3*x^6*y^2 + 9*x^6*z^2 - 12*x^4*y^2*z^2 + 9*x^2*y^6 - 12*x^2*y^4*z^2 - 12*x^2*y^2*z^4 + 3*x^2*z^6 + 3*y^6*z^2 + 9*y^2*z^6) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * x^6 * (z - x)^2 + (96 : ℝ) * x^6 * (z - x)^1 * (y - z)^1 + (96 : ℝ) * x^6 * (y - z)^2 + (384 : ℝ) * x^5 * (z - x)^3 + (504 : ℝ) * x^5 * (z - x)^2 * (y - z)^1 + (504 : ℝ) * x^5 * (z - x)^1 * (y - z)^2 + (192 : ℝ) * x^5 * (y - z)^3 + (648 : ℝ) * x^4 * (z - x)^4 + (1056 : ℝ) * x^4 * (z - x)^3 * (y - z)^1 + (1104 : ℝ) * x^4 * (z - x)^2 * (y - z)^2 + (696 : ℝ) * x^4 * (z - x)^1 * (y - z)^3 + (168 : ℝ) * x^4 * (y - z)^4 + (600 : ℝ) * x^3 * (z - x)^5 + (1170 : ℝ) * x^3 * (z - x)^4 * (y - z)^1 + (1284 : ℝ) * x^3 * (z - x)^3 * (y - z)^2 + (996 : ℝ) * x^3 * (z - x)^2 * (y - z)^3 + (426 : ℝ) * x^3 * (z - x)^1 * (y - z)^4 + (72 : ℝ) * x^3 * (y - z)^5 + (324 : ℝ) * x^2 * (z - x)^6 + (738 : ℝ) * x^2 * (z - x)^5 * (y - z)^1 + (861 : ℝ) * x^2 * (z - x)^4 * (y - z)^2 + (732 : ℝ) * x^2 * (z - x)^3 * (y - z)^3 + (393 : ℝ) * x^2 * (z - x)^2 * (y - z)^4 + (108 : ℝ) * x^2 * (z - x)^1 * (y - z)^5 + (12 : ℝ) * x^2 * (y - z)^6 + (96 : ℝ) * x^1 * (z - x)^7 + (252 : ℝ) * x^1 * (z - x)^6 * (y - z)^1 + (324 : ℝ) * x^1 * (z - x)^5 * (y - z)^2 + (300 : ℝ) * x^1 * (z - x)^4 * (y - z)^3 + (180 : ℝ) * x^1 * (z - x)^3 * (y - z)^4 + (54 : ℝ) * x^1 * (z - x)^2 * (y - z)^5 + (6 : ℝ) * x^1 * (z - x)^1 * (y - z)^6 + (12 : ℝ) * (z - x)^8 + (36 : ℝ) * (z - x)^7 * (y - z)^1 + (54 : ℝ) * (z - x)^6 * (y - z)^2 + (60 : ℝ) * (z - x)^5 * (y - z)^3 + (45 : ℝ) * (z - x)^4 * (y - z)^4 + (18 : ℝ) * (z - x)^3 * (y - z)^5 + (3 : ℝ) * (z - x)^2 * (y - z)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*x^6*y^2 + 9*x^6*z^2 - 12*x^4*y^2*z^2 + 9*x^2*y^6 - 12*x^2*y^4*z^2 - 12*x^2*y^2*z^4 + 3*x^2*z^6 + 3*y^6*z^2 + 9*y^2*z^6) := by
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
  have hn : 0 ≤ (3*x^6*y^2 + 9*x^6*z^2 - 12*x^4*y^2*z^2 + 9*x^2*y^6 - 12*x^2*y^4*z^2 - 12*x^2*y^2*z^4 + 3*x^2*z^6 + 3*y^6*z^2 + 9*y^2*z^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x^2 * (x^2 - y^2) / (x^2 + 3 * y^2) + y^2 * (y^2 - z^2) / (y^2 + 3 * z^2) + z^2 * (z^2 - x^2) / (z^2 + 3 * x^2) ≥ 0) := @solution
#print axioms solution
