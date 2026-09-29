-- Prove2me | solution 1 for WorkbookSource.base_28549
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:03:53.927693+00:00
-- url     : https://prove2.me/submissions/796fae08-fd4f-483f-b685-1378bcb2d648

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 / (2 * a + 1) + b^2 / (2 * b + 1) + c^2 / (2 * c + 1) ≤ 3 * (a^2 + b^2 + c^2) / (2 * (a^2 + b^2 + c^2) + 3)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b/9 + 2*a^5*c/9 + 32*a^4*b*c/9 - 4*a^3*b^3/9 - 2*a^3*b^2*c/9 - 2*a^3*b*c^2/9 - 4*a^3*c^3/9 - 2*a^2*b^3*c/9 - 28*a^2*b^2*c^2/3 - 2*a^2*b*c^3/9 + 2*a*b^5/9 + 32*a*b^4*c/9 - 2*a*b^3*c^2/9 - 2*a*b^2*c^3/9 + 32*a*b*c^4/9 + 2*a*c^5/9 + 2*b^5*c/9 - 4*b^3*c^3/9 + 2*b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (92/3 : ℝ) * a^3 * (b - a)^3 + (46 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (50 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (52/3 : ℝ) * a^3 * (c - b)^3 + (232/9 : ℝ) * a^2 * (b - a)^4 + (464/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (190/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (338/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (52/9 : ℝ) * a^2 * (c - b)^4 + (64/9 : ℝ) * a^1 * (b - a)^5 + (160/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (236/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (194/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (62/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/9 : ℝ) * a^1 * (c - b)^5 + (8/9 : ℝ) * (b - a)^4 * (c - b)^2 + (16/9 : ℝ) * (b - a)^3 * (c - b)^3 + (10/9 : ℝ) * (b - a)^2 * (c - b)^4 + (2/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b/9 + 2*a^5*c/9 + 32*a^4*b*c/9 - 4*a^3*b^3/9 - 2*a^3*b^2*c/9 - 2*a^3*b*c^2/9 - 4*a^3*c^3/9 - 2*a^2*b^3*c/9 - 28*a^2*b^2*c^2/3 - 2*a^2*b*c^3/9 + 2*a*b^5/9 + 32*a*b^4*c/9 - 2*a*b^3*c^2/9 - 2*a*b^2*c^3/9 + 32*a*b*c^4/9 + 2*a*c^5/9 + 2*b^5*c/9 - 4*b^3*c^3/9 + 2*b*c^5/9) := by
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
  have he : (-8*a^4*b*c - 4*a^4*b - 4*a^4*c - 2*a^4 - 8*a^3*b^2*c - 4*a^3*b^2 - 8*a^3*b*c^2 + 24*a^3*b*c + 12*a^3*b - 4*a^3*c^2 + 12*a^3*c + 6*a^3 - 8*a^2*b^3*c - 4*a^2*b^3 - 8*a^2*b^2*c - 4*a^2*b^2 - 8*a^2*b*c^3 - 8*a^2*b*c^2 - 4*a^2*c^3 - 4*a^2*c^2 - 8*a*b^4*c - 4*a*b^4 - 8*a*b^3*c^2 + 24*a*b^3*c + 12*a*b^3 - 8*a*b^2*c^3 - 8*a*b^2*c^2 - 8*a*b*c^4 + 24*a*b*c^3 - 4*a*c^4 + 12*a*c^3 - 4*b^4*c - 2*b^4 - 4*b^3*c^2 + 12*b^3*c + 6*b^3 - 4*b^2*c^3 - 4*b^2*c^2 - 4*b*c^4 + 12*b*c^3 - 2*c^4 + 6*c^3) = (2*a^5*b/9 + 2*a^5*c/9 + 32*a^4*b*c/9 - 4*a^3*b^3/9 - 2*a^3*b^2*c/9 - 2*a^3*b*c^2/9 - 4*a^3*c^3/9 - 2*a^2*b^3*c/9 - 28*a^2*b^2*c^2/3 - 2*a^2*b*c^3/9 + 2*a*b^5/9 + 32*a*b^4*c/9 - 2*a*b^3*c^2/9 - 2*a*b^2*c^3/9 + 32*a*b*c^4/9 + 2*a*c^5/9 + 2*b^5*c/9 - 4*b^3*c^3/9 + 2*b*c^5/9) := by
    linear_combination (-2*a^4*b/9 - 2*a^4*c/9 + 2*a^3*b^2/9 - 100*a^3*b*c/9 - 14*a^3*b/3 + 2*a^3*c^2/9 - 14*a^3*c/3 - 2*a^3 + 2*a^2*b^3/9 + 28*a^2*b^2*c/9 + 4*a^2*b^2/3 + 28*a^2*b*c^2/9 + 2*a^2*c^3/9 + 4*a^2*c^2/3 - 2*a*b^4/9 - 100*a*b^3*c/9 - 14*a*b^3/3 + 28*a*b^2*c^2/9 - 100*a*b*c^3/9 - 2*a*c^4/9 - 14*a*c^3/3 - 2*b^4*c/9 + 2*b^3*c^2/9 - 14*b^3*c/3 - 2*b^3 + 2*b^2*c^3/9 + 4*b^2*c^2/3 - 2*b*c^4/9 - 14*b*c^3/3 - 2*c^3) * habc
  have hn : 0 ≤ (-8*a^4*b*c - 4*a^4*b - 4*a^4*c - 2*a^4 - 8*a^3*b^2*c - 4*a^3*b^2 - 8*a^3*b*c^2 + 24*a^3*b*c + 12*a^3*b - 4*a^3*c^2 + 12*a^3*c + 6*a^3 - 8*a^2*b^3*c - 4*a^2*b^3 - 8*a^2*b^2*c - 4*a^2*b^2 - 8*a^2*b*c^3 - 8*a^2*b*c^2 - 4*a^2*c^3 - 4*a^2*c^2 - 8*a*b^4*c - 4*a*b^4 - 8*a*b^3*c^2 + 24*a*b^3*c + 12*a*b^3 - 8*a*b^2*c^3 - 8*a*b^2*c^2 - 8*a*b*c^4 + 24*a*b*c^3 - 4*a*c^4 + 12*a*c^3 - 4*b^4*c - 2*b^4 - 4*b^3*c^2 + 12*b^3*c + 6*b^3 - 4*b^2*c^3 - 4*b^2*c^2 - 4*b*c^4 + 12*b*c^3 - 2*c^4 + 6*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^2 / (2 * a + 1) + b^2 / (2 * b + 1) + c^2 / (2 * c + 1) ≤ 3 * (a^2 + b^2 + c^2) / (2 * (a^2 + b^2 + c^2) + 3)) := @solution
#print axioms solution
