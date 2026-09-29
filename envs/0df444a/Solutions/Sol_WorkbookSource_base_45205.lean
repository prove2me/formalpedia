-- Prove2me | solution 1 for WorkbookSource.base_45205
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:57:02.258199+00:00
-- url     : https://prove2.me/submissions/c18bb0fe-e825-43cb-ba1e-b18e46ac9f10

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (343 / 8) ≥ (6 * (x / (x + y)) + y / (y + z)) * (6 * (y / (y + z)) + z / (z + x)) * (6 * (z / (z + x)) + x / (x + y))  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (7*x^4*y^2 + 398*x^4*y*z + 343*x^4*z^2 + 638*x^3*y^3 - 686*x^3*y^2*z - 350*x^3*y*z^2 + 638*x^3*z^3 + 343*x^2*y^4 - 350*x^2*y^3*z - 1050*x^2*y^2*z^2 - 686*x^2*y*z^3 + 7*x^2*z^4 + 398*x*y^4*z - 686*x*y^3*z^2 - 350*x*y^2*z^3 + 398*x*y*z^4 + 7*y^4*z^2 + 638*y^3*z^3 + 343*y^2*z^4) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (3472 : ℝ) * x^4 * (y - x)^2 + (3472 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (3472 : ℝ) * x^4 * (z - y)^2 + (10656 : ℝ) * x^3 * (y - x)^3 + (17496 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (13304 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (3232 : ℝ) * x^3 * (z - y)^3 + (11884 : ℝ) * x^2 * (y - x)^4 + (26792 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (22764 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (7856 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (748 : ℝ) * x^2 * (z - y)^4 + (5688 : ℝ) * x^1 * (y - x)^5 + (16068 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (16568 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (7272 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (1084 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (988 : ℝ) * (y - x)^6 + (3300 : ℝ) * (y - x)^5 * (z - y)^1 + (3979 : ℝ) * (y - x)^4 * (z - y)^2 + (2010 : ℝ) * (y - x)^3 * (z - y)^3 + (343 : ℝ) * (y - x)^2 * (z - y)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ z) (hord2 : z ≤ y) : 0 ≤ (7*x^4*y^2 + 398*x^4*y*z + 343*x^4*z^2 + 638*x^3*y^3 - 686*x^3*y^2*z - 350*x^3*y*z^2 + 638*x^3*z^3 + 343*x^2*y^4 - 350*x^2*y^3*z - 1050*x^2*y^2*z^2 - 686*x^2*y*z^3 + 7*x^2*z^4 + 398*x*y^4*z - 686*x*y^3*z^2 - 350*x*y^2*z^3 + 398*x*y*z^4 + 7*y^4*z^2 + 638*y^3*z^3 + 343*y^2*z^4) := by
    have hdiff1 : 0 ≤ (z - x) := by linarith
    have hdiff2 : 0 ≤ (y - z) := by linarith
    have hpos : 0 ≤ (3472 : ℝ) * x^4 * (z - x)^2 + (3472 : ℝ) * x^4 * (z - x)^1 * (y - z)^1 + (3472 : ℝ) * x^4 * (y - z)^2 + (10656 : ℝ) * x^3 * (z - x)^3 + (14472 : ℝ) * x^3 * (z - x)^2 * (y - z)^1 + (10280 : ℝ) * x^3 * (z - x)^1 * (y - z)^2 + (3232 : ℝ) * x^3 * (y - z)^3 + (11884 : ℝ) * x^2 * (z - x)^4 + (20744 : ℝ) * x^2 * (z - x)^3 * (y - z)^1 + (13692 : ℝ) * x^2 * (z - x)^2 * (y - z)^2 + (4832 : ℝ) * x^2 * (z - x)^1 * (y - z)^3 + (748 : ℝ) * x^2 * (y - z)^4 + (5688 : ℝ) * x^1 * (z - x)^5 + (12372 : ℝ) * x^1 * (z - x)^4 * (y - z)^1 + (9176 : ℝ) * x^1 * (z - x)^3 * (y - z)^2 + (2904 : ℝ) * x^1 * (z - x)^2 * (y - z)^3 + (412 : ℝ) * x^1 * (z - x)^1 * (y - z)^4 + (988 : ℝ) * (z - x)^6 + (2628 : ℝ) * (z - x)^5 * (y - z)^1 + (2299 : ℝ) * (z - x)^4 * (y - z)^2 + (666 : ℝ) * (z - x)^3 * (y - z)^3 + (7 : ℝ) * (z - x)^2 * (y - z)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (7*x^4*y^2 + 398*x^4*y*z + 343*x^4*z^2 + 638*x^3*y^3 - 686*x^3*y^2*z - 350*x^3*y*z^2 + 638*x^3*z^3 + 343*x^2*y^4 - 350*x^2*y^3*z - 1050*x^2*y^2*z^2 - 686*x^2*y*z^3 + 7*x^2*z^4 + 398*x*y^4*z - 686*x*y^3*z^2 - 350*x*y^2*z^3 + 398*x*y*z^4 + 7*y^4*z^2 + 638*y^3*z^3 + 343*y^2*z^4) := by
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
  have hn : 0 ≤ (7*x^4*y^2 + 398*x^4*y*z + 343*x^4*z^2 + 638*x^3*y^3 - 686*x^3*y^2*z - 350*x^3*y*z^2 + 638*x^3*z^3 + 343*x^2*y^4 - 350*x^2*y^3*z - 1050*x^2*y^2*z^2 - 686*x^2*y*z^3 + 7*x^2*z^4 + 398*x*y^4*z - 686*x*y^3*z^2 - 350*x*y^2*z^3 + 398*x*y*z^4 + 7*y^4*z^2 + 638*y^3*z^3 + 343*y^2*z^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (343 / 8) ≥ (6 * (x / (x + y)) + y / (y + z)) * (6 * (y / (y + z)) + z / (z + x)) * (6 * (z / (z + x)) + x / (x + y))) := @solution
#print axioms solution
