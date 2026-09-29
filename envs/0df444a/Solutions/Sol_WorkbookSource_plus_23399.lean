-- Prove2me | solution 1 for WorkbookSource.plus_23399
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:42:07.782749+00:00
-- url     : https://prove2.me/submissions/1346eef9-47fa-4a7b-8b94-5751249f3251

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + 3) + b / (b + 3) + c / (c + 3) + 1 / (a * b + b * c + a * c) ≥ 13 / 12   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^5/3 + 2*a^4*b/3 + 2*a^4*c/3 - a^3*b^2/3 - 12*a^3*b*c - a^3*c^2/3 - a^2*b^3/3 + 26*a^2*b^2*c/3 + 26*a^2*b*c^2/3 - a^2*c^3/3 + 2*a*b^4/3 - 12*a*b^3*c + 26*a*b^2*c^2/3 - 12*a*b*c^3 + 2*a*c^4/3 + 8*b^5/3 + 2*b^4*c/3 - b^3*c^2/3 - b^2*c^3/3 + 2*b*c^4/3 + 8*c^5/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40/3 : ℝ) * a^3 * (b - a)^2 + (40/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (40/3 : ℝ) * a^3 * (c - b)^2 + (62/3 : ℝ) * a^2 * (b - a)^3 + (31 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (49 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (58/3 : ℝ) * a^2 * (c - b)^3 + (16 : ℝ) * a^1 * (b - a)^4 + (32 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (194/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (146/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (44/3 : ℝ) * a^1 * (c - b)^4 + (6 : ℝ) * (b - a)^5 + (15 : ℝ) * (b - a)^4 * (c - b)^1 + (88/3 : ℝ) * (b - a)^3 * (c - b)^2 + (29 : ℝ) * (b - a)^2 * (c - b)^3 + (14 : ℝ) * (b - a)^1 * (c - b)^4 + (8/3 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^5/3 + 2*a^4*b/3 + 2*a^4*c/3 - a^3*b^2/3 - 12*a^3*b*c - a^3*c^2/3 - a^2*b^3/3 + 26*a^2*b^2*c/3 + 26*a^2*b*c^2/3 - a^2*c^3/3 + 2*a*b^4/3 - 12*a*b^3*c + 26*a*b^2*c^2/3 - 12*a*b*c^3 + 2*a*c^4/3 + 8*b^5/3 + 2*b^4*c/3 - b^3*c^2/3 - b^2*c^3/3 + 2*b*c^4/3 + 8*c^5/3) := by
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
  have he : (23*a^2*b^2*c + 33*a^2*b^2 + 23*a^2*b*c^2 + 66*a^2*b*c - 9*a^2*b + 33*a^2*c^2 - 9*a^2*c + 23*a*b^2*c^2 + 66*a*b^2*c - 9*a*b^2 + 66*a*b*c^2 - 15*a*b*c - 315*a*b - 9*a*c^2 - 315*a*c + 108*a + 33*b^2*c^2 - 9*b^2*c - 9*b*c^2 - 315*b*c + 108*b + 108*c + 324) = (8*a^5/3 + 2*a^4*b/3 + 2*a^4*c/3 - a^3*b^2/3 - 12*a^3*b*c - a^3*c^2/3 - a^2*b^3/3 + 26*a^2*b^2*c/3 + 26*a^2*b*c^2/3 - a^2*c^3/3 + 2*a*b^4/3 - 12*a*b^3*c + 26*a*b^2*c^2/3 - 12*a*b*c^3 + 2*a*c^4/3 + 8*b^5/3 + 2*b^4*c/3 - b^3*c^2/3 - b^2*c^3/3 + 2*b*c^4/3 + 8*c^5/3) := by
    linear_combination (-8*a^4/3 + 2*a^3*b + 2*a^3*c - 8*a^3 - 5*a^2*b^2/3 + 8*a^2*b*c + 14*a^2*b - 5*a^2*c^2/3 + 14*a^2*c - 24*a^2 + 2*a*b^3 + 8*a*b^2*c + 14*a*b^2 + 8*a*b*c^2 + 62*a*b*c + 57*a*b + 2*a*c^3 + 14*a*c^2 + 57*a*c - 72*a - 8*b^4/3 + 2*b^3*c - 8*b^3 - 5*b^2*c^2/3 + 14*b^2*c - 24*b^2 + 2*b*c^3 + 14*b*c^2 + 57*b*c - 72*b - 8*c^4/3 - 8*c^3 - 24*c^2 - 72*c - 108) * hab
  have hn : 0 ≤ (23*a^2*b^2*c + 33*a^2*b^2 + 23*a^2*b*c^2 + 66*a^2*b*c - 9*a^2*b + 33*a^2*c^2 - 9*a^2*c + 23*a*b^2*c^2 + 66*a*b^2*c - 9*a*b^2 + 66*a*b*c^2 - 15*a*b*c - 315*a*b - 9*a*c^2 - 315*a*c + 108*a + 33*b^2*c^2 - 9*b^2*c - 9*b*c^2 - 315*b*c + 108*b + 108*c + 324) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (a + 3) + b / (b + 3) + c / (c + 3) + 1 / (a * b + b * c + a * c) ≥ 13 / 12) := @solution
#print axioms solution
