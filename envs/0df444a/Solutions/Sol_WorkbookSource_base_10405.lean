-- Prove2me | solution 1 for WorkbookSource.base_10405
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:32:32.476325+00:00
-- url     : https://prove2.me/submissions/239ad127-9ff8-4671-8ef7-1e806339ab6e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a ^ 4 + b ^ 4 + c ^ 4 + (15 / 4) * (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≥ (23 / 8) * (a ^ 2 + b ^ 2 + c ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (49*a^6*b/9 + 49*a^6*c/9 + 13*a^5*b^2/9 + 4*a^5*b*c + 13*a^5*c^2/9 - 62*a^4*b^3/9 - 31*a^4*b^2*c/9 - 31*a^4*b*c^2/9 - 62*a^4*c^3/9 - 62*a^3*b^4/9 - 4*a^3*b^3*c + 62*a^3*b^2*c^2/9 - 4*a^3*b*c^3 - 62*a^3*c^4/9 + 13*a^2*b^5/9 - 31*a^2*b^4*c/9 + 62*a^2*b^3*c^2/9 + 62*a^2*b^2*c^3/9 - 31*a^2*b*c^4/9 + 13*a^2*c^5/9 + 49*a*b^6/9 + 4*a*b^5*c - 31*a*b^4*c^2/9 - 4*a*b^3*c^3 - 31*a*b^2*c^4/9 + 4*a*b*c^5 + 49*a*c^6/9 + 49*b^6*c/9 + 13*b^5*c^2/9 - 62*b^4*c^3/9 - 62*b^3*c^4/9 + 13*b^2*c^5/9 + 49*b*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (220/3 : ℝ) * a^5 * (b - a)^2 + (220/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (220/3 : ℝ) * a^5 * (c - b)^2 + (1598/9 : ℝ) * a^4 * (b - a)^3 + (799/3 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (467 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (1702/9 : ℝ) * a^4 * (c - b)^3 + (154 : ℝ) * a^3 * (b - a)^4 + (308 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (7978/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (6592/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (1594/9 : ℝ) * a^3 * (c - b)^4 + (520/9 : ℝ) * a^2 * (b - a)^5 + (1300/9 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (6472/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (8408/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (4016/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (650/9 : ℝ) * a^2 * (c - b)^5 + (8 : ℝ) * a^1 * (b - a)^6 + (24 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (790/3 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (1460/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (3098/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (944/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (98/9 : ℝ) * a^1 * (c - b)^6 + (320/9 : ℝ) * (b - a)^5 * (c - b)^2 + (800/9 : ℝ) * (b - a)^4 * (c - b)^3 + (82 : ℝ) * (b - a)^3 * (c - b)^4 + (307/9 : ℝ) * (b - a)^2 * (c - b)^5 + (49/9 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (49*a^6*b/9 + 49*a^6*c/9 + 13*a^5*b^2/9 + 4*a^5*b*c + 13*a^5*c^2/9 - 62*a^4*b^3/9 - 31*a^4*b^2*c/9 - 31*a^4*b*c^2/9 - 62*a^4*c^3/9 - 62*a^3*b^4/9 - 4*a^3*b^3*c + 62*a^3*b^2*c^2/9 - 4*a^3*b*c^3 - 62*a^3*c^4/9 + 13*a^2*b^5/9 - 31*a^2*b^4*c/9 + 62*a^2*b^3*c^2/9 + 62*a^2*b^2*c^3/9 - 31*a^2*b*c^4/9 + 13*a^2*c^5/9 + 49*a*b^6/9 + 4*a*b^5*c - 31*a*b^4*c^2/9 - 4*a*b^3*c^3 - 31*a*b^2*c^4/9 + 4*a*b*c^5 + 49*a*c^6/9 + 49*b^6*c/9 + 13*b^5*c^2/9 - 62*b^4*c^3/9 - 62*b^3*c^4/9 + 13*b^2*c^5/9 + 49*b*c^6/9) := by
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
  have he : (8*a^6*b + 8*a^6*c + 8*a^5*b^2 + 16*a^5*b*c + 8*a^5*c^2 + 8*a^4*b^2*c + 8*a^4*b*c^2 - 23*a^4*b - 23*a^4*c - 23*a^3*b^2 - 46*a^3*b*c - 23*a^3*c^2 + 8*a^2*b^5 + 8*a^2*b^4*c - 23*a^2*b^3 - 46*a^2*b^2*c + 30*a^2*b^2 + 8*a^2*b*c^4 - 46*a^2*b*c^2 + 90*a^2*b*c + 8*a^2*c^5 - 23*a^2*c^3 + 30*a^2*c^2 + 8*a*b^6 + 16*a*b^5*c + 8*a*b^4*c^2 - 23*a*b^4 - 46*a*b^3*c + 8*a*b^2*c^4 - 46*a*b^2*c^2 + 90*a*b^2*c + 16*a*b*c^5 - 46*a*b*c^3 + 90*a*b*c^2 + 8*a*c^6 - 23*a*c^4 + 8*b^6*c + 8*b^5*c^2 - 23*b^4*c - 23*b^3*c^2 + 8*b^2*c^5 - 23*b^2*c^3 + 30*b^2*c^2 + 8*b*c^6 - 23*b*c^4) = (49*a^6*b/9 + 49*a^6*c/9 + 13*a^5*b^2/9 + 4*a^5*b*c + 13*a^5*c^2/9 - 62*a^4*b^3/9 - 31*a^4*b^2*c/9 - 31*a^4*b*c^2/9 - 62*a^4*c^3/9 - 62*a^3*b^4/9 - 4*a^3*b^3*c + 62*a^3*b^2*c^2/9 - 4*a^3*b*c^3 - 62*a^3*c^4/9 + 13*a^2*b^5/9 - 31*a^2*b^4*c/9 + 62*a^2*b^3*c^2/9 + 62*a^2*b^2*c^3/9 - 31*a^2*b*c^4/9 + 13*a^2*c^5/9 + 49*a*b^6/9 + 4*a*b^5*c - 31*a*b^4*c^2/9 - 4*a*b^3*c^3 - 31*a*b^2*c^4/9 + 4*a*b*c^5 + 49*a*c^6/9 + 49*b^6*c/9 + 13*b^5*c^2/9 - 62*b^4*c^3/9 - 62*b^3*c^4/9 + 13*b^2*c^5/9 + 49*b*c^6/9) := by
    linear_combination (23*a^5*b/9 + 23*a^5*c/9 + 4*a^4*b^2 + 62*a^4*b*c/9 + 23*a^4*b/3 + 4*a^4*c^2 + 23*a^4*c/3 + 26*a^3*b^3/9 + 5*a^3*b^2*c/9 + 13*a^3*b^2/3 + 5*a^3*b*c^2/9 + 16*a^3*b*c/3 + 26*a^3*c^3/9 + 13*a^3*c^2/3 + 4*a^2*b^4 + 5*a^2*b^3*c/9 + 13*a^2*b^3/3 - 8*a^2*b^2*c^2 - 8*a^2*b^2*c - 10*a^2*b^2 + 5*a^2*b*c^3/9 - 8*a^2*b*c^2 - 30*a^2*b*c + 4*a^2*c^4 + 13*a^2*c^3/3 - 10*a^2*c^2 + 23*a*b^5/9 + 62*a*b^4*c/9 + 23*a*b^4/3 + 5*a*b^3*c^2/9 + 16*a*b^3*c/3 + 5*a*b^2*c^3/9 - 8*a*b^2*c^2 - 30*a*b^2*c + 62*a*b*c^4/9 + 16*a*b*c^3/3 - 30*a*b*c^2 + 23*a*c^5/9 + 23*a*c^4/3 + 23*b^5*c/9 + 4*b^4*c^2 + 23*b^4*c/3 + 26*b^3*c^3/9 + 13*b^3*c^2/3 + 4*b^2*c^4 + 13*b^2*c^3/3 - 10*b^2*c^2 + 23*b*c^5/9 + 23*b*c^4/3) * habc
  have hn : 0 ≤ (8*a^6*b + 8*a^6*c + 8*a^5*b^2 + 16*a^5*b*c + 8*a^5*c^2 + 8*a^4*b^2*c + 8*a^4*b*c^2 - 23*a^4*b - 23*a^4*c - 23*a^3*b^2 - 46*a^3*b*c - 23*a^3*c^2 + 8*a^2*b^5 + 8*a^2*b^4*c - 23*a^2*b^3 - 46*a^2*b^2*c + 30*a^2*b^2 + 8*a^2*b*c^4 - 46*a^2*b*c^2 + 90*a^2*b*c + 8*a^2*c^5 - 23*a^2*c^3 + 30*a^2*c^2 + 8*a*b^6 + 16*a*b^5*c + 8*a*b^4*c^2 - 23*a*b^4 - 46*a*b^3*c + 8*a*b^2*c^4 - 46*a*b^2*c^2 + 90*a*b^2*c + 16*a*b*c^5 - 46*a*b*c^3 + 90*a*b*c^2 + 8*a*c^6 - 23*a*c^4 + 8*b^6*c + 8*b^5*c^2 - 23*b^4*c - 23*b^3*c^2 + 8*b^2*c^5 - 23*b^2*c^3 + 30*b^2*c^2 + 8*b*c^6 - 23*b*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a ^ 4 + b ^ 4 + c ^ 4 + (15 / 4) * (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≥ (23 / 8) * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
