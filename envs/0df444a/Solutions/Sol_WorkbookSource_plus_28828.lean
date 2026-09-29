-- Prove2me | solution 1 for WorkbookSource.plus_28828
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:44.612707+00:00
-- url     : https://prove2.me/submissions/81dd3335-6062-4d45-9bb8-770bc4b7c102

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 4 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b) * (b + c) * (c + a) * (a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^6*b/3 + 10*a^6*c/3 + 2*a^5*b^2 + 13*a^5*b*c/3 + 2*a^5*c^2 - 7*a^4*b^3/3 - 4*a^4*b^2*c/3 - 4*a^4*b*c^2/3 - 7*a^4*c^3/3 - 7*a^3*b^4/3 - 13*a^3*b^3*c/3 - 10*a^3*b^2*c^2/3 - 13*a^3*b*c^3/3 - 7*a^3*c^4/3 + 2*a^2*b^5 - 4*a^2*b^4*c/3 - 10*a^2*b^3*c^2/3 - 10*a^2*b^2*c^3/3 - 4*a^2*b*c^4/3 + 2*a^2*c^5 + 10*a*b^6/3 + 13*a*b^5*c/3 - 4*a*b^4*c^2/3 - 13*a*b^3*c^3/3 - 4*a*b^2*c^4/3 + 13*a*b*c^5/3 + 10*a*c^6/3 + 10*b^6*c/3 + 2*b^5*c^2 - 7*b^4*c^3/3 - 7*b^3*c^4/3 + 2*b^2*c^5 + 10*b*c^6/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (84 : ℝ) * a^5 * (b - a)^2 + (84 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (84 : ℝ) * a^5 * (c - b)^2 + (748/3 : ℝ) * a^4 * (b - a)^3 + (374 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (466 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (512/3 : ℝ) * a^4 * (c - b)^3 + (875/3 : ℝ) * a^3 * (b - a)^4 + (1750/3 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (2705/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (610 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (403/3 : ℝ) * a^3 * (c - b)^4 + (512/3 : ℝ) * a^2 * (b - a)^5 + (1280/3 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (2378/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (2287/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (967/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (145/3 : ℝ) * a^2 * (c - b)^5 + (151/3 : ℝ) * a^1 * (b - a)^6 + (151 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (326 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (1201/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (730/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (205/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (20/3 : ℝ) * a^1 * (c - b)^6 + (6 : ℝ) * (b - a)^7 + (21 : ℝ) * (b - a)^6 * (c - b)^1 + (51 : ℝ) * (b - a)^5 * (c - b)^2 + (75 : ℝ) * (b - a)^4 * (c - b)^3 + (173/3 : ℝ) * (b - a)^3 * (c - b)^4 + (22 : ℝ) * (b - a)^2 * (c - b)^5 + (10/3 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^6*b/3 + 10*a^6*c/3 + 2*a^5*b^2 + 13*a^5*b*c/3 + 2*a^5*c^2 - 7*a^4*b^3/3 - 4*a^4*b^2*c/3 - 4*a^4*b*c^2/3 - 7*a^4*c^3/3 - 7*a^3*b^4/3 - 13*a^3*b^3*c/3 - 10*a^3*b^2*c^2/3 - 13*a^3*b*c^3/3 - 7*a^3*c^4/3 + 2*a^2*b^5 - 4*a^2*b^4*c/3 - 10*a^2*b^3*c^2/3 - 10*a^2*b^2*c^3/3 - 4*a^2*b*c^4/3 + 2*a^2*c^5 + 10*a*b^6/3 + 13*a*b^5*c/3 - 4*a*b^4*c^2/3 - 13*a*b^3*c^3/3 - 4*a*b^2*c^4/3 + 13*a*b*c^5/3 + 10*a*c^6/3 + 10*b^6*c/3 + 2*b^5*c^2 - 7*b^4*c^3/3 - 7*b^3*c^4/3 + 2*b^2*c^5 + 10*b*c^6/3) := by
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
  have he : (4*a^6*b + 4*a^6*c + 4*a^5*b^2 + 8*a^5*b*c + 4*a^5*c^2 + 4*a^4*b^2*c + 4*a^4*b*c^2 + a^4*b*c - 6*a^4*b - 6*a^4*c + a^3*b^3 + 5*a^3*b^2*c - 6*a^3*b^2 + 5*a^3*b*c^2 - 12*a^3*b*c + a^3*c^3 - 6*a^3*c^2 + 4*a^2*b^5 + 4*a^2*b^4*c + 5*a^2*b^3*c - 6*a^2*b^3 + 12*a^2*b^2*c^2 - 12*a^2*b^2*c + 4*a^2*b*c^4 + 5*a^2*b*c^3 - 12*a^2*b*c^2 + 4*a^2*c^5 - 6*a^2*c^3 + 4*a*b^6 + 8*a*b^5*c + 4*a*b^4*c^2 + a*b^4*c - 6*a*b^4 + 5*a*b^3*c^2 - 12*a*b^3*c + 4*a*b^2*c^4 + 5*a*b^2*c^3 - 12*a*b^2*c^2 + 8*a*b*c^5 + a*b*c^4 - 12*a*b*c^3 + 4*a*c^6 - 6*a*c^4 + 4*b^6*c + 4*b^5*c^2 - 6*b^4*c + b^3*c^3 - 6*b^3*c^2 + 4*b^2*c^5 - 6*b^2*c^3 + 4*b*c^6 - 6*b*c^4) = (10*a^6*b/3 + 10*a^6*c/3 + 2*a^5*b^2 + 13*a^5*b*c/3 + 2*a^5*c^2 - 7*a^4*b^3/3 - 4*a^4*b^2*c/3 - 4*a^4*b*c^2/3 - 7*a^4*c^3/3 - 7*a^3*b^4/3 - 13*a^3*b^3*c/3 - 10*a^3*b^2*c^2/3 - 13*a^3*b*c^3/3 - 7*a^3*c^4/3 + 2*a^2*b^5 - 4*a^2*b^4*c/3 - 10*a^2*b^3*c^2/3 - 10*a^2*b^2*c^3/3 - 4*a^2*b*c^4/3 + 2*a^2*c^5 + 10*a*b^6/3 + 13*a*b^5*c/3 - 4*a*b^4*c^2/3 - 13*a*b^3*c^3/3 - 4*a*b^2*c^4/3 + 13*a*b*c^5/3 + 10*a*c^6/3 + 10*b^6*c/3 + 2*b^5*c^2 - 7*b^4*c^3/3 - 7*b^3*c^4/3 + 2*b^2*c^5 + 10*b*c^6/3) := by
    linear_combination (2*a^5*b/3 + 2*a^5*c/3 + 4*a^4*b^2/3 + 7*a^4*b*c/3 + 2*a^4*b + 4*a^4*c^2/3 + 2*a^4*c + a^3*b^3 + 5*a^3*b^2*c/3 + 2*a^3*b^2 + 5*a^3*b*c^2/3 + 4*a^3*b*c + a^3*c^3 + 2*a^3*c^2 + 4*a^2*b^4/3 + 5*a^2*b^3*c/3 + 2*a^2*b^3 + 4*a^2*b^2*c + 5*a^2*b*c^3/3 + 4*a^2*b*c^2 + 4*a^2*c^4/3 + 2*a^2*c^3 + 2*a*b^5/3 + 7*a*b^4*c/3 + 2*a*b^4 + 5*a*b^3*c^2/3 + 4*a*b^3*c + 5*a*b^2*c^3/3 + 4*a*b^2*c^2 + 7*a*b*c^4/3 + 4*a*b*c^3 + 2*a*c^5/3 + 2*a*c^4 + 2*b^5*c/3 + 4*b^4*c^2/3 + 2*b^4*c + b^3*c^3 + 2*b^3*c^2 + 4*b^2*c^4/3 + 2*b^2*c^3 + 2*b*c^5/3 + 2*b*c^4) * habc
  have hn : 0 ≤ (4*a^6*b + 4*a^6*c + 4*a^5*b^2 + 8*a^5*b*c + 4*a^5*c^2 + 4*a^4*b^2*c + 4*a^4*b*c^2 + a^4*b*c - 6*a^4*b - 6*a^4*c + a^3*b^3 + 5*a^3*b^2*c - 6*a^3*b^2 + 5*a^3*b*c^2 - 12*a^3*b*c + a^3*c^3 - 6*a^3*c^2 + 4*a^2*b^5 + 4*a^2*b^4*c + 5*a^2*b^3*c - 6*a^2*b^3 + 12*a^2*b^2*c^2 - 12*a^2*b^2*c + 4*a^2*b*c^4 + 5*a^2*b*c^3 - 12*a^2*b*c^2 + 4*a^2*c^5 - 6*a^2*c^3 + 4*a*b^6 + 8*a*b^5*c + 4*a*b^4*c^2 + a*b^4*c - 6*a*b^4 + 5*a*b^3*c^2 - 12*a*b^3*c + 4*a*b^2*c^4 + 5*a*b^2*c^3 - 12*a*b^2*c^2 + 8*a*b*c^5 + a*b*c^4 - 12*a*b*c^3 + 4*a*c^6 - 6*a*c^4 + 4*b^6*c + 4*b^5*c^2 - 6*b^4*c + b^3*c^3 - 6*b^3*c^2 + 4*b^2*c^5 - 6*b^2*c^3 + 4*b*c^6 - 6*b*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 4 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b) * (b + c) * (c + a) * (a * b / (a + b) ^ 2 + b * c / (b + c) ^ 2 + c * a / (c + a) ^ 2) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
