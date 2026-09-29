-- Prove2me | solution 1 for WorkbookSource.base_15777
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:05.67192+00:00
-- url     : https://prove2.me/submissions/f475ff35-ffec-4d0c-954d-5226e98bbd87

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (a^2 + a - b * c) * (b^2 + b - c * a) * (c^2 + c - a * b) ≤ 8  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^6/729 + 16*a^5*b/243 + 16*a^5*c/243 + 148*a^4*b^2/243 - 280*a^4*b*c/243 + 148*a^4*c^2/243 + 1537*a^3*b^3/729 + 25*a^3*b^2*c/243 + 25*a^3*b*c^2/243 + 1537*a^3*c^3/729 + 148*a^2*b^4/243 + 25*a^2*b^3*c/243 - 46*a^2*b^2*c^2/81 + 25*a^2*b*c^3/243 + 148*a^2*c^4/243 + 16*a*b^5/243 - 280*a*b^4*c/243 + 25*a*b^3*c^2/243 + 25*a*b^2*c^3/243 - 280*a*b*c^4/243 + 16*a*c^5/243 + 8*b^6/729 + 16*b^5*c/243 + 148*b^4*c^2/243 + 1537*b^3*c^3/729 + 148*b^2*c^4/243 + 16*b*c^5/243 + 8*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * a^6 + (28 : ℝ) * a^5 * (b - a)^1 + (14 : ℝ) * a^5 * (c - b)^1 + (51 : ℝ) * a^4 * (b - a)^2 + (51 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^4 * (c - b)^2 + (520/9 : ℝ) * a^3 * (b - a)^3 + (260/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (124/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (56/9 : ℝ) * a^3 * (c - b)^3 + (389/9 : ℝ) * a^2 * (b - a)^4 + (778/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (163/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (100/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8/9 : ℝ) * a^2 * (c - b)^4 + (1532/81 : ℝ) * a^1 * (b - a)^5 + (3830/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (3224/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1006/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (112/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (16/81 : ℝ) * a^1 * (c - b)^5 + (2537/729 : ℝ) * (b - a)^6 + (2537/243 : ℝ) * (b - a)^5 * (c - b)^1 + (2773/243 : ℝ) * (b - a)^4 * (c - b)^2 + (3953/729 : ℝ) * (b - a)^3 * (c - b)^3 + (268/243 : ℝ) * (b - a)^2 * (c - b)^4 + (32/243 : ℝ) * (b - a)^1 * (c - b)^5 + (8/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^6/729 + 16*a^5*b/243 + 16*a^5*c/243 + 148*a^4*b^2/243 - 280*a^4*b*c/243 + 148*a^4*c^2/243 + 1537*a^3*b^3/729 + 25*a^3*b^2*c/243 + 25*a^3*b*c^2/243 + 1537*a^3*c^3/729 + 148*a^2*b^4/243 + 25*a^2*b^3*c/243 - 46*a^2*b^2*c^2/81 + 25*a^2*b*c^3/243 + 148*a^2*c^4/243 + 16*a*b^5/243 - 280*a*b^4*c/243 + 25*a*b^3*c^2/243 + 25*a*b^2*c^3/243 - 280*a*b*c^4/243 + 16*a*c^5/243 + 8*b^6/729 + 16*b^5*c/243 + 148*b^4*c^2/243 + 1537*b^3*c^3/729 + 148*b^2*c^4/243 + 16*b*c^5/243 + 8*c^6/729) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-a^4*b*c + a^3*b^3 + a^3*b^2 - a^3*b*c + a^3*c^3 + a^3*c^2 + a^2*b^3 - a^2*b^2*c + a^2*b^2 - a^2*b*c^2 - a^2*b*c + a^2*c^3 + a^2*c^2 - a*b^4*c - a*b^3*c - a*b^2*c^2 - a*b^2*c - a*b*c^4 - a*b*c^3 - a*b*c^2 - a*b*c + b^3*c^3 + b^3*c^2 + b^2*c^3 + b^2*c^2 + 8) = (8*a^6/729 + 16*a^5*b/243 + 16*a^5*c/243 + 148*a^4*b^2/243 - 280*a^4*b*c/243 + 148*a^4*c^2/243 + 1537*a^3*b^3/729 + 25*a^3*b^2*c/243 + 25*a^3*b*c^2/243 + 1537*a^3*c^3/729 + 148*a^2*b^4/243 + 25*a^2*b^3*c/243 - 46*a^2*b^2*c^2/81 + 25*a^2*b*c^3/243 + 148*a^2*c^4/243 + 16*a*b^5/243 - 280*a*b^4*c/243 + 25*a*b^3*c^2/243 + 25*a*b^2*c^3/243 - 280*a*b*c^4/243 + 16*a*c^5/243 + 8*b^6/729 + 16*b^5*c/243 + 148*b^4*c^2/243 + 1537*b^3*c^3/729 + 148*b^2*c^4/243 + 16*b*c^5/243 + 8*c^6/729) := by
    linear_combination (-8*a^5/729 - 40*a^4*b/729 - 40*a^4*c/729 - 8*a^4/243 - 404*a^3*b^2/729 + 191*a^3*b*c/729 - 32*a^3*b/243 - 404*a^3*c^2/729 - 32*a^3*c/243 - 8*a^3/81 - 404*a^2*b^3/729 + 46*a^2*b^2*c/243 - 43*a^2*b^2/81 + 46*a^2*b*c^2/243 + 4*a^2*b*c/81 - 8*a^2*b/27 - 404*a^2*c^3/729 - 43*a^2*c^2/81 - 8*a^2*c/27 - 8*a^2/27 - 40*a*b^4/729 + 191*a*b^3*c/729 - 32*a*b^3/243 + 46*a*b^2*c^2/243 + 4*a*b^2*c/81 - 8*a*b^2/27 + 191*a*b*c^3/729 + 4*a*b*c^2/81 - 7*a*b*c/27 - 16*a*b/27 - 40*a*c^4/729 - 32*a*c^3/243 - 8*a*c^2/27 - 16*a*c/27 - 8*a/9 - 8*b^5/729 - 40*b^4*c/729 - 8*b^4/243 - 404*b^3*c^2/729 - 32*b^3*c/243 - 8*b^3/81 - 404*b^2*c^3/729 - 43*b^2*c^2/81 - 8*b^2*c/27 - 8*b^2/27 - 40*b*c^4/729 - 32*b*c^3/243 - 8*b*c^2/27 - 16*b*c/27 - 8*b/9 - 8*c^5/729 - 8*c^4/243 - 8*c^3/81 - 8*c^2/27 - 8*c/9 - 8/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), (a^2 + a - b * c) * (b^2 + b - c * a) * (c^2 + c - a * b) ≤ 8) := @solution
#print axioms solution
