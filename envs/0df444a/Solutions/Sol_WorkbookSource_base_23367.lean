-- Prove2me | solution 1 for WorkbookSource.base_23367
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:55:11.728569+00:00
-- url     : https://prove2.me/submissions/793085d2-3586-4e16-b11b-dc4ca31081c4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + b) / (2 * a * b + 1) + (b + c) / (2 * b * c + 1) + (a + c) / (2 * a * c + 1) ≥ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6/729 + 14*a^5*b/243 + 14*a^5*c/243 + 44*a^4*b^2/243 - 68*a^4*b*c/243 + 44*a^4*c^2/243 + 188*a^3*b^3/729 + 374*a^3*b^2*c/243 + 374*a^3*b*c^2/243 + 188*a^3*c^3/729 + 44*a^2*b^4/243 + 374*a^2*b^3*c/243 - 860*a^2*b^2*c^2/81 + 374*a^2*b*c^3/243 + 44*a^2*c^4/243 + 14*a*b^5/243 - 68*a*b^4*c/243 + 374*a*b^3*c^2/243 + 374*a*b^2*c^3/243 - 68*a*b*c^4/243 + 14*a*c^5/243 + 4*b^6/729 + 14*b^5*c/243 + 44*b^4*c^2/243 + 188*b^3*c^3/729 + 44*b^2*c^4/243 + 14*b*c^5/243 + 4*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16/3 : ℝ) * a^4 * (b - a)^2 + (16/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16/3 : ℝ) * a^4 * (c - b)^2 + (436/27 : ℝ) * a^3 * (b - a)^3 + (218/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (166/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (140/27 : ℝ) * a^3 * (c - b)^3 + (464/27 : ℝ) * a^2 * (b - a)^4 + (928/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (238/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (250/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (20/27 : ℝ) * a^2 * (c - b)^4 + (64/9 : ℝ) * a^1 * (b - a)^5 + (160/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (428/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (6 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (10/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/27 : ℝ) * a^1 * (c - b)^5 + (544/729 : ℝ) * (b - a)^6 + (544/243 : ℝ) * (b - a)^5 * (c - b)^1 + (656/243 : ℝ) * (b - a)^4 * (c - b)^2 + (1216/729 : ℝ) * (b - a)^3 * (c - b)^3 + (134/243 : ℝ) * (b - a)^2 * (c - b)^4 + (22/243 : ℝ) * (b - a)^1 * (c - b)^5 + (4/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6/729 + 14*a^5*b/243 + 14*a^5*c/243 + 44*a^4*b^2/243 - 68*a^4*b*c/243 + 44*a^4*c^2/243 + 188*a^3*b^3/729 + 374*a^3*b^2*c/243 + 374*a^3*b*c^2/243 + 188*a^3*c^3/729 + 44*a^2*b^4/243 + 374*a^2*b^3*c/243 - 860*a^2*b^2*c^2/81 + 374*a^2*b*c^3/243 + 44*a^2*c^4/243 + 14*a*b^5/243 - 68*a*b^4*c/243 + 374*a*b^3*c^2/243 + 374*a*b^2*c^3/243 - 68*a*b*c^4/243 + 14*a*c^5/243 + 4*b^6/729 + 14*b^5*c/243 + 44*b^4*c^2/243 + 188*b^3*c^3/729 + 44*b^2*c^4/243 + 14*b*c^5/243 + 4*c^6/729) := by
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
  have he : (-16*a^2*b^2*c^2 + 8*a^2*b^2*c + 8*a^2*b*c^2 - 8*a^2*b*c + 2*a^2*b + 2*a^2*c + 8*a*b^2*c^2 - 8*a*b^2*c + 2*a*b^2 - 8*a*b*c^2 + 12*a*b*c - 4*a*b + 2*a*c^2 - 4*a*c + 2*a + 2*b^2*c + 2*b*c^2 - 4*b*c + 2*b + 2*c - 2) = (4*a^6/729 + 14*a^5*b/243 + 14*a^5*c/243 + 44*a^4*b^2/243 - 68*a^4*b*c/243 + 44*a^4*c^2/243 + 188*a^3*b^3/729 + 374*a^3*b^2*c/243 + 374*a^3*b*c^2/243 + 188*a^3*c^3/729 + 44*a^2*b^4/243 + 374*a^2*b^3*c/243 - 860*a^2*b^2*c^2/81 + 374*a^2*b*c^3/243 + 44*a^2*c^4/243 + 14*a*b^5/243 - 68*a*b^4*c/243 + 374*a*b^3*c^2/243 + 374*a*b^2*c^3/243 - 68*a*b*c^4/243 + 14*a*c^5/243 + 4*b^6/729 + 14*b^5*c/243 + 44*b^4*c^2/243 + 188*b^3*c^3/729 + 44*b^2*c^4/243 + 14*b*c^5/243 + 4*c^6/729) := by
    linear_combination (-4*a^5/729 - 38*a^4*b/729 - 38*a^4*c/729 - 4*a^4/243 - 94*a^3*b^2/729 + 280*a^3*b*c/729 - 34*a^3*b/243 - 94*a^3*c^2/729 - 34*a^3*c/243 - 4*a^3/81 - 94*a^2*b^3/729 - 436*a^2*b^2*c/243 - 20*a^2*b^2/81 - 436*a^2*b*c^2/243 + 116*a^2*b*c/81 - 10*a^2*b/27 - 94*a^2*c^3/729 - 20*a^2*c^2/81 - 10*a^2*c/27 - 4*a^2/27 - 38*a*b^4/729 + 280*a*b^3*c/729 - 34*a*b^3/243 - 436*a*b^2*c^2/243 + 116*a*b^2*c/81 - 10*a*b^2/27 + 280*a*b*c^3/729 + 116*a*b*c^2/81 - 80*a*b*c/27 + 28*a*b/27 - 38*a*c^4/729 - 34*a*c^3/243 - 10*a*c^2/27 + 28*a*c/27 - 4*a/9 - 4*b^5/729 - 38*b^4*c/729 - 4*b^4/243 - 94*b^3*c^2/729 - 34*b^3*c/243 - 4*b^3/81 - 94*b^2*c^3/729 - 20*b^2*c^2/81 - 10*b^2*c/27 - 4*b^2/27 - 38*b*c^4/729 - 34*b*c^3/243 - 10*b*c^2/27 + 28*b*c/27 - 4*b/9 - 4*c^5/729 - 4*c^4/243 - 4*c^3/81 - 4*c^2/27 - 4*c/9 + 2/3) * habc
  have hn : 0 ≤ (-16*a^2*b^2*c^2 + 8*a^2*b^2*c + 8*a^2*b*c^2 - 8*a^2*b*c + 2*a^2*b + 2*a^2*c + 8*a*b^2*c^2 - 8*a*b^2*c + 2*a*b^2 - 8*a*b*c^2 + 12*a*b*c - 4*a*b + 2*a*c^2 - 4*a*c + 2*a + 2*b^2*c + 2*b*c^2 - 4*b*c + 2*b + 2*c - 2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a + b) / (2 * a * b + 1) + (b + c) / (2 * b * c + 1) + (a + c) / (2 * a * c + 1) ≥ 2) := @solution
#print axioms solution
