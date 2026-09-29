-- Prove2me | solution 1 for WorkbookSource.base_19817
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:44:28.032334+00:00
-- url     : https://prove2.me/submissions/2a14ddff-ff92-4ab4-81e5-5b8e1c0fa658

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * (x / (y + z) + y / (x + z) + z / (x + y)) - 1)^2 - 1 ≥ 2 * (x + y + z)^2 / (x^2 + y^2 + z^2 + x * y + y * z + z * x)  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (4*x^8 + 8*x^7*y + 8*x^7*z + 10*x^6*y^2 + 24*x^6*y*z + 10*x^6*z^2 + 8*x^5*y^3 + 12*x^5*y^2*z + 12*x^5*y*z^2 + 8*x^5*z^3 + 4*x^4*y^4 - 8*x^4*y^3*z - 28*x^4*y^2*z^2 - 8*x^4*y*z^3 + 4*x^4*z^4 + 8*x^3*y^5 - 8*x^3*y^4*z - 64*x^3*y^3*z^2 - 64*x^3*y^2*z^3 - 8*x^3*y*z^4 + 8*x^3*z^5 + 10*x^2*y^6 + 12*x^2*y^5*z - 28*x^2*y^4*z^2 - 64*x^2*y^3*z^3 - 28*x^2*y^2*z^4 + 12*x^2*y*z^5 + 10*x^2*z^6 + 8*x*y^7 + 24*x*y^6*z + 12*x*y^5*z^2 - 8*x*y^4*z^3 - 8*x*y^3*z^4 + 12*x*y^2*z^5 + 24*x*y*z^6 + 8*x*z^7 + 4*y^8 + 8*y^7*z + 10*y^6*z^2 + 8*y^5*z^3 + 4*y^4*z^4 + 8*y^3*z^5 + 10*y^2*z^6 + 8*y*z^7 + 4*z^8) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (832 : ℝ) * x^6 * (y - x)^2 + (832 : ℝ) * x^6 * (y - x)^1 * (z - y)^1 + (832 : ℝ) * x^6 * (z - y)^2 + (3200 : ℝ) * x^5 * (y - x)^3 + (4800 : ℝ) * x^5 * (y - x)^2 * (z - y)^1 + (5184 : ℝ) * x^5 * (y - x)^1 * (z - y)^2 + (1792 : ℝ) * x^5 * (z - y)^3 + (5184 : ℝ) * x^4 * (y - x)^4 + (10368 : ℝ) * x^4 * (y - x)^3 * (z - y)^1 + (12992 : ℝ) * x^4 * (y - x)^2 * (z - y)^2 + (7808 : ℝ) * x^4 * (y - x)^1 * (z - y)^3 + (1664 : ℝ) * x^4 * (z - y)^4 + (4512 : ℝ) * x^3 * (y - x)^5 + (11280 : ℝ) * x^3 * (y - x)^4 * (z - y)^1 + (16544 : ℝ) * x^3 * (y - x)^3 * (z - y)^2 + (13536 : ℝ) * x^3 * (y - x)^2 * (z - y)^3 + (5488 : ℝ) * x^3 * (y - x)^1 * (z - y)^4 + (864 : ℝ) * x^3 * (z - y)^5 + (2220 : ℝ) * x^2 * (y - x)^6 + (6660 : ℝ) * x^2 * (y - x)^5 * (z - y)^1 + (11342 : ℝ) * x^2 * (y - x)^4 * (z - y)^2 + (11584 : ℝ) * x^2 * (y - x)^3 * (z - y)^3 + (6782 : ℝ) * x^2 * (y - x)^2 * (z - y)^4 + (2100 : ℝ) * x^2 * (y - x)^1 * (z - y)^5 + (268 : ℝ) * x^2 * (z - y)^6 + (584 : ℝ) * x^1 * (y - x)^7 + (2044 : ℝ) * x^1 * (y - x)^6 * (z - y)^1 + (3996 : ℝ) * x^1 * (y - x)^5 * (z - y)^2 + (4880 : ℝ) * x^1 * (y - x)^4 * (z - y)^3 + (3708 : ℝ) * x^1 * (y - x)^3 * (z - y)^4 + (1704 : ℝ) * x^1 * (y - x)^2 * (z - y)^5 + (436 : ℝ) * x^1 * (y - x)^1 * (z - y)^6 + (48 : ℝ) * x^1 * (z - y)^7 + (64 : ℝ) * (y - x)^8 + (256 : ℝ) * (y - x)^7 * (z - y)^1 + (568 : ℝ) * (y - x)^6 * (z - y)^2 + (808 : ℝ) * (y - x)^5 * (z - y)^3 + (754 : ℝ) * (y - x)^4 * (z - y)^4 + (460 : ℝ) * (y - x)^3 * (z - y)^5 + (178 : ℝ) * (y - x)^2 * (z - y)^6 + (40 : ℝ) * (y - x)^1 * (z - y)^7 + (4 : ℝ) * (z - y)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*x^8 + 8*x^7*y + 8*x^7*z + 10*x^6*y^2 + 24*x^6*y*z + 10*x^6*z^2 + 8*x^5*y^3 + 12*x^5*y^2*z + 12*x^5*y*z^2 + 8*x^5*z^3 + 4*x^4*y^4 - 8*x^4*y^3*z - 28*x^4*y^2*z^2 - 8*x^4*y*z^3 + 4*x^4*z^4 + 8*x^3*y^5 - 8*x^3*y^4*z - 64*x^3*y^3*z^2 - 64*x^3*y^2*z^3 - 8*x^3*y*z^4 + 8*x^3*z^5 + 10*x^2*y^6 + 12*x^2*y^5*z - 28*x^2*y^4*z^2 - 64*x^2*y^3*z^3 - 28*x^2*y^2*z^4 + 12*x^2*y*z^5 + 10*x^2*z^6 + 8*x*y^7 + 24*x*y^6*z + 12*x*y^5*z^2 - 8*x*y^4*z^3 - 8*x*y^3*z^4 + 12*x*y^2*z^5 + 24*x*y*z^6 + 8*x*z^7 + 4*y^8 + 8*y^7*z + 10*y^6*z^2 + 8*y^5*z^3 + 4*y^4*z^4 + 8*y^3*z^5 + 10*y^2*z^6 + 8*y*z^7 + 4*z^8) := by
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
  have hn : 0 ≤ (4*x^8 + 8*x^7*y + 8*x^7*z + 10*x^6*y^2 + 24*x^6*y*z + 10*x^6*z^2 + 8*x^5*y^3 + 12*x^5*y^2*z + 12*x^5*y*z^2 + 8*x^5*z^3 + 4*x^4*y^4 - 8*x^4*y^3*z - 28*x^4*y^2*z^2 - 8*x^4*y*z^3 + 4*x^4*z^4 + 8*x^3*y^5 - 8*x^3*y^4*z - 64*x^3*y^3*z^2 - 64*x^3*y^2*z^3 - 8*x^3*y*z^4 + 8*x^3*z^5 + 10*x^2*y^6 + 12*x^2*y^5*z - 28*x^2*y^4*z^2 - 64*x^2*y^3*z^3 - 28*x^2*y^2*z^4 + 12*x^2*y*z^5 + 10*x^2*z^6 + 8*x*y^7 + 24*x*y^6*z + 12*x*y^5*z^2 - 8*x*y^4*z^3 - 8*x*y^3*z^4 + 12*x*y^2*z^5 + 24*x*y*z^6 + 8*x*z^7 + 4*y^8 + 8*y^7*z + 10*y^6*z^2 + 8*y^5*z^3 + 4*y^4*z^4 + 8*y^3*z^5 + 10*y^2*z^6 + 8*y*z^7 + 4*z^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (2 * (x / (y + z) + y / (x + z) + z / (x + y)) - 1)^2 - 1 ≥ 2 * (x + y + z)^2 / (x^2 + y^2 + z^2 + x * y + y * z + z * x)) := @solution
#print axioms solution
