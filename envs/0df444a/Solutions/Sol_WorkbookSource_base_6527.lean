-- Prove2me | solution 1 for WorkbookSource.base_6527
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:19:11.077545+00:00
-- url     : https://prove2.me/submissions/fb2f5147-975e-48d7-bc4b-b52ae906a4f8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) :  x ^ 6 + y ^ 6 + z ^ 6 + 3 ≥ (3 / 32) * (x + y) ^ 2 * (y + z) ^ 2 * (x + z) ^ 2  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (7808*x^6/243 + 64*x^5*y/81 + 64*x^5*z/81 - 83*x^4*y^2/81 - 166*x^4*y*z/81 - 83*x^4*z^2/81 - 818*x^3*y^3/243 - 818*x^3*y^2*z/81 - 818*x^3*y*z^2/81 - 818*x^3*z^3/243 - 83*x^2*y^4/81 - 818*x^2*y^3*z/81 - 490*x^2*y^2*z^2/27 - 818*x^2*y*z^3/81 - 83*x^2*z^4/81 + 64*x*y^5/81 - 166*x*y^4*z/81 - 818*x*y^3*z^2/81 - 818*x*y^2*z^3/81 - 166*x*y*z^4/81 + 64*x*z^5/81 + 7808*y^6/243 + 64*y^5*z/81 - 83*y^4*z^2/81 - 818*y^3*z^3/243 - 83*y^2*z^4/81 + 64*y*z^5/81 + 7808*z^6/243) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (352 : ℝ) * x^4 * (y - x)^2 + (352 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (352 : ℝ) * x^4 * (z - y)^2 + (7136/9 : ℝ) * x^3 * (y - x)^3 + (3568/3 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (4880/3 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (5536/9 : ℝ) * x^3 * (z - y)^3 + (6772/9 : ℝ) * x^2 * (y - x)^4 + (13544/9 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (7940/3 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (17048/9 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (4372/9 : ℝ) * x^2 * (z - y)^4 + (9176/27 : ℝ) * x^1 * (y - x)^5 + (22940/27 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (49832/27 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (51808/27 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (26236/27 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (5248/27 : ℝ) * x^1 * (z - y)^5 + (14684/243 : ℝ) * (y - x)^6 + (14684/81 : ℝ) * (y - x)^5 * (z - y)^1 + (38281/81 : ℝ) * (y - x)^4 * (z - y)^2 + (156266/243 : ℝ) * (y - x)^3 * (z - y)^3 + (39277/81 : ℝ) * (y - x)^2 * (z - y)^4 + (15680/81 : ℝ) * (y - x)^1 * (z - y)^5 + (7808/243 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (7808*x^6/243 + 64*x^5*y/81 + 64*x^5*z/81 - 83*x^4*y^2/81 - 166*x^4*y*z/81 - 83*x^4*z^2/81 - 818*x^3*y^3/243 - 818*x^3*y^2*z/81 - 818*x^3*y*z^2/81 - 818*x^3*z^3/243 - 83*x^2*y^4/81 - 818*x^2*y^3*z/81 - 490*x^2*y^2*z^2/27 - 818*x^2*y*z^3/81 - 83*x^2*z^4/81 + 64*x*y^5/81 - 166*x*y^4*z/81 - 818*x*y^3*z^2/81 - 818*x*y^2*z^3/81 - 166*x*y*z^4/81 + 64*x*z^5/81 + 7808*y^6/243 + 64*y^5*z/81 - 83*y^4*z^2/81 - 818*y^3*z^3/243 - 83*y^2*z^4/81 + 64*y*z^5/81 + 7808*z^6/243) := by
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
  have he : (32*x^6 - 3*x^4*y^2 - 6*x^4*y*z - 3*x^4*z^2 - 6*x^3*y^3 - 18*x^3*y^2*z - 18*x^3*y*z^2 - 6*x^3*z^3 - 3*x^2*y^4 - 18*x^2*y^3*z - 30*x^2*y^2*z^2 - 18*x^2*y*z^3 - 3*x^2*z^4 - 6*x*y^4*z - 18*x*y^3*z^2 - 18*x*y^2*z^3 - 6*x*y*z^4 + 32*y^6 - 3*y^4*z^2 - 6*y^3*z^3 - 3*y^2*z^4 + 32*z^6 + 96) = (7808*x^6/243 + 64*x^5*y/81 + 64*x^5*z/81 - 83*x^4*y^2/81 - 166*x^4*y*z/81 - 83*x^4*z^2/81 - 818*x^3*y^3/243 - 818*x^3*y^2*z/81 - 818*x^3*y*z^2/81 - 818*x^3*z^3/243 - 83*x^2*y^4/81 - 818*x^2*y^3*z/81 - 490*x^2*y^2*z^2/27 - 818*x^2*y*z^3/81 - 83*x^2*z^4/81 + 64*x*y^5/81 - 166*x*y^4*z/81 - 818*x*y^3*z^2/81 - 818*x*y^2*z^3/81 - 166*x*y*z^4/81 + 64*x*z^5/81 + 7808*y^6/243 + 64*y^5*z/81 - 83*y^4*z^2/81 - 818*y^3*z^3/243 - 83*y^2*z^4/81 + 64*y*z^5/81 + 7808*z^6/243) := by
    linear_combination (-32*x^5/243 - 160*x^4*y/243 - 160*x^4*z/243 - 32*x^4/81 - 320*x^3*y^2/243 - 640*x^3*y*z/243 - 128*x^3*y/81 - 320*x^3*z^2/243 - 128*x^3*z/81 - 32*x^3/27 - 320*x^2*y^3/243 - 320*x^2*y^2*z/81 - 64*x^2*y^2/27 - 320*x^2*y*z^2/81 - 128*x^2*y*z/27 - 32*x^2*y/9 - 320*x^2*z^3/243 - 64*x^2*z^2/27 - 32*x^2*z/9 - 32*x^2/9 - 160*x*y^4/243 - 640*x*y^3*z/243 - 128*x*y^3/81 - 320*x*y^2*z^2/81 - 128*x*y^2*z/27 - 32*x*y^2/9 - 640*x*y*z^3/243 - 128*x*y*z^2/27 - 64*x*y*z/9 - 64*x*y/9 - 160*x*z^4/243 - 128*x*z^3/81 - 32*x*z^2/9 - 64*x*z/9 - 32*x/3 - 32*y^5/243 - 160*y^4*z/243 - 32*y^4/81 - 320*y^3*z^2/243 - 128*y^3*z/81 - 32*y^3/27 - 320*y^2*z^3/243 - 64*y^2*z^2/27 - 32*y^2*z/9 - 32*y^2/9 - 160*y*z^4/243 - 128*y*z^3/81 - 32*y*z^2/9 - 64*y*z/9 - 32*y/3 - 32*z^5/243 - 32*z^4/81 - 32*z^3/27 - 32*z^2/9 - 32*z/3 - 32) * h
  have hn : 0 ≤ (32*x^6 - 3*x^4*y^2 - 6*x^4*y*z - 3*x^4*z^2 - 6*x^3*y^3 - 18*x^3*y^2*z - 18*x^3*y*z^2 - 6*x^3*z^3 - 3*x^2*y^4 - 18*x^2*y^3*z - 30*x^2*y^2*z^2 - 18*x^2*y*z^3 - 3*x^2*z^4 - 6*x*y^4*z - 18*x*y^3*z^2 - 18*x*y^2*z^3 - 6*x*y*z^4 + 32*y^6 - 3*y^4*z^2 - 6*y^3*z^3 - 3*y^2*z^4 + 32*z^6 + 96) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), x ^ 6 + y ^ 6 + z ^ 6 + 3 ≥ (3 / 32) * (x + y) ^ 2 * (y + z) ^ 2 * (x + z) ^ 2) := @solution
#print axioms solution
