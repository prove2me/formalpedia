-- Prove2me | solution 1 for WorkbookSource.base_37690
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:40.27013+00:00
-- url     : https://prove2.me/submissions/babec723-20c0-4cc3-b7ec-ebf66161169b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hx1 : x + y + z = 3) : 1 / (4 + (x + y) ^ 2) + 1 / (4 + (y + z) ^ 2) + 1 / (4 + (z + x) ^ 2) ≥ 3 / 8  := by
  have haux0 (x y z : ℝ) (hlow : 0 ≤ x) (hord1 : x ≤ y) (hord2 : y ≤ z) : 0 ≤ (52*x^6/243 + 16*x^5*y/9 + 16*x^5*z/9 + 47*x^4*y^2/27 + 178*x^4*y*z/81 + 47*x^4*z^2/27 + 86*x^3*y^3/243 - 86*x^3*y^2*z/27 - 86*x^3*y*z^2/27 + 86*x^3*z^3/243 + 47*x^2*y^4/27 - 86*x^2*y^3*z/27 - 278*x^2*y^2*z^2/27 - 86*x^2*y*z^3/27 + 47*x^2*z^4/27 + 16*x*y^5/9 + 178*x*y^4*z/81 - 86*x*y^3*z^2/27 - 86*x*y^2*z^3/27 + 178*x*y*z^4/81 + 16*x*z^5/9 + 52*y^6/243 + 16*y^5*z/9 + 47*y^4*z^2/27 + 86*y^3*z^3/243 + 47*y^2*z^4/27 + 16*y*z^5/9 + 52*z^6/243) := by
    have hdiff1 : 0 ≤ (y - x) := by linarith
    have hdiff2 : 0 ≤ (z - y) := by linarith
    have hpos : 0 ≤ (128/3 : ℝ) * x^4 * (y - x)^2 + (128/3 : ℝ) * x^4 * (y - x)^1 * (z - y)^1 + (128/3 : ℝ) * x^4 * (z - y)^2 + (1024/9 : ℝ) * x^3 * (y - x)^3 + (512/3 : ℝ) * x^3 * (y - x)^2 * (z - y)^1 + (512/3 : ℝ) * x^3 * (y - x)^1 * (z - y)^2 + (512/9 : ℝ) * x^3 * (z - y)^3 + (112 : ℝ) * x^2 * (y - x)^4 + (224 : ℝ) * x^2 * (y - x)^3 * (z - y)^1 + (752/3 : ℝ) * x^2 * (y - x)^2 * (z - y)^2 + (416/3 : ℝ) * x^2 * (y - x)^1 * (z - y)^3 + (80/3 : ℝ) * x^2 * (z - y)^4 + (3928/81 : ℝ) * x^1 * (y - x)^5 + (9820/81 : ℝ) * x^1 * (y - x)^4 * (z - y)^1 + (12568/81 : ℝ) * x^1 * (y - x)^3 * (z - y)^2 + (9032/81 : ℝ) * x^1 * (y - x)^2 * (z - y)^3 + (3140/81 : ℝ) * x^1 * (y - x)^1 * (z - y)^4 + (392/81 : ℝ) * x^1 * (z - y)^5 + (1900/243 : ℝ) * (y - x)^6 + (1900/81 : ℝ) * (y - x)^5 * (z - y)^1 + (2773/81 : ℝ) * (y - x)^4 * (z - y)^2 + (7138/243 : ℝ) * (y - x)^3 * (z - y)^3 + (1121/81 : ℝ) * (y - x)^2 * (z - y)^4 + (248/81 : ℝ) * (y - x)^1 * (z - y)^5 + (52/243 : ℝ) * (z - y)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (52*x^6/243 + 16*x^5*y/9 + 16*x^5*z/9 + 47*x^4*y^2/27 + 178*x^4*y*z/81 + 47*x^4*z^2/27 + 86*x^3*y^3/243 - 86*x^3*y^2*z/27 - 86*x^3*y*z^2/27 + 86*x^3*z^3/243 + 47*x^2*y^4/27 - 86*x^2*y^3*z/27 - 278*x^2*y^2*z^2/27 - 86*x^2*y*z^3/27 + 47*x^2*z^4/27 + 16*x*y^5/9 + 178*x*y^4*z/81 - 86*x*y^3*z^2/27 - 86*x*y^2*z^3/27 + 178*x*y*z^4/81 + 16*x*z^5/9 + 52*y^6/243 + 16*y^5*z/9 + 47*y^4*z^2/27 + 86*y^3*z^3/243 + 47*y^2*z^4/27 + 16*y*z^5/9 + 52*z^6/243) := by
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
  have he : (-3*x^4*y^2 - 6*x^4*y*z - 3*x^4*z^2 - 4*x^4 - 6*x^3*y^3 - 18*x^3*y^2*z - 18*x^3*y*z^2 - 8*x^3*y - 6*x^3*z^3 - 8*x^3*z - 3*x^2*y^4 - 18*x^2*y^3*z - 30*x^2*y^2*z^2 - 12*x^2*y^2 - 18*x^2*y*z^3 - 32*x^2*y*z - 3*x^2*z^4 - 12*x^2*z^2 + 32*x^2 - 6*x*y^4*z - 18*x*y^3*z^2 - 8*x*y^3 - 18*x*y^2*z^3 - 32*x*y^2*z - 6*x*y*z^4 - 32*x*y*z^2 + 32*x*y - 8*x*z^3 + 32*x*z - 3*y^4*z^2 - 4*y^4 - 6*y^3*z^3 - 8*y^3*z - 3*y^2*z^4 - 12*y^2*z^2 + 32*y^2 - 8*y*z^3 + 32*y*z - 4*z^4 + 32*z^2 + 192) = (52*x^6/243 + 16*x^5*y/9 + 16*x^5*z/9 + 47*x^4*y^2/27 + 178*x^4*y*z/81 + 47*x^4*z^2/27 + 86*x^3*y^3/243 - 86*x^3*y^2*z/27 - 86*x^3*y*z^2/27 + 86*x^3*z^3/243 + 47*x^2*y^4/27 - 86*x^2*y^3*z/27 - 278*x^2*y^2*z^2/27 - 86*x^2*y*z^3/27 + 47*x^2*z^4/27 + 16*x*y^5/9 + 178*x*y^4*z/81 - 86*x*y^3*z^2/27 - 86*x*y^2*z^3/27 + 178*x*y*z^4/81 + 16*x*z^5/9 + 52*y^6/243 + 16*y^5*z/9 + 47*y^4*z^2/27 + 86*y^3*z^3/243 + 47*y^2*z^4/27 + 16*y*z^5/9 + 52*z^6/243) := by
    linear_combination (-52*x^5/243 - 380*x^4*y/243 - 380*x^4*z/243 - 52*x^4/81 - 772*x^3*y^2/243 - 1232*x^3*y*z/243 - 328*x^3*y/81 - 772*x^3*z^2/243 - 328*x^3*z/81 - 160*x^3/27 - 772*x^2*y^3/243 - 532*x^2*y^2*z/81 - 148*x^2*y^2/27 - 532*x^2*y*z^2/81 - 64*x^2*y*z/9 - 128*x^2*y/9 - 772*x^2*z^3/243 - 148*x^2*z^2/27 - 128*x^2*z/9 - 160*x^2/9 - 380*x*y^4/243 - 1232*x*y^3*z/243 - 328*x*y^3/81 - 532*x*y^2*z^2/81 - 64*x*y^2*z/9 - 128*x*y^2/9 - 1232*x*y*z^3/243 - 64*x*y*z^2/9 - 224*x*y*z/9 - 224*x*y/9 - 380*x*z^4/243 - 328*x*z^3/81 - 128*x*z^2/9 - 224*x*z/9 - 64*x/3 - 52*y^5/243 - 380*y^4*z/243 - 52*y^4/81 - 772*y^3*z^2/243 - 328*y^3*z/81 - 160*y^3/27 - 772*y^2*z^3/243 - 148*y^2*z^2/27 - 128*y^2*z/9 - 160*y^2/9 - 380*y*z^4/243 - 328*y*z^3/81 - 128*y*z^2/9 - 224*y*z/9 - 64*y/3 - 52*z^5/243 - 52*z^4/81 - 160*z^3/27 - 160*z^2/9 - 64*z/3 - 64) * hx1
  have hn : 0 ≤ (-3*x^4*y^2 - 6*x^4*y*z - 3*x^4*z^2 - 4*x^4 - 6*x^3*y^3 - 18*x^3*y^2*z - 18*x^3*y*z^2 - 8*x^3*y - 6*x^3*z^3 - 8*x^3*z - 3*x^2*y^4 - 18*x^2*y^3*z - 30*x^2*y^2*z^2 - 12*x^2*y^2 - 18*x^2*y*z^3 - 32*x^2*y*z - 3*x^2*z^4 - 12*x^2*z^2 + 32*x^2 - 6*x*y^4*z - 18*x*y^3*z^2 - 8*x*y^3 - 18*x*y^2*z^3 - 32*x*y^2*z - 6*x*y*z^4 - 32*x*y*z^2 + 32*x*y - 8*x*z^3 + 32*x*z - 3*y^4*z^2 - 4*y^4 - 6*y^3*z^3 - 8*y^3*z - 3*y^2*z^4 - 12*y^2*z^2 + 32*y^2 - 8*y*z^3 + 32*y*z - 4*z^4 + 32*z^2 + 192) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hx1 : x + y + z = 3), 1 / (4 + (x + y) ^ 2) + 1 / (4 + (y + z) ^ 2) + 1 / (4 + (z + x) ^ 2) ≥ 3 / 8) := @solution
#print axioms solution
