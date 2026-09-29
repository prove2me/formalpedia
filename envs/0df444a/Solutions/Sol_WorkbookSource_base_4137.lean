-- Prove2me | solution 1 for WorkbookSource.base_4137
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:11:38.48884+00:00
-- url     : https://prove2.me/submissions/85453e7c-26d5-421b-98fb-d7217ba0535c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) :  a * b * c + 15 / (a * b + b * c + c * a) ≥ 6  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^5/81 + 7*a^4*b/81 + 7*a^4*c/81 - 4*a^3*b^2/81 - 26*a^3*b*c/81 - 4*a^3*c^2/81 - 4*a^2*b^3/81 + 5*a^2*b^2*c/27 + 5*a^2*b*c^2/27 - 4*a^2*c^3/81 + 7*a*b^4/81 - 26*a*b^3*c/81 + 5*a*b^2*c^2/27 - 26*a*b*c^3/81 + 7*a*c^4/81 + 5*b^5/81 + 7*b^4*c/81 - 4*b^3*c^2/81 - 4*b^2*c^3/81 + 7*b*c^4/81 + 5*c^5/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^3 * (b - a)^2 + (2/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (2/3 : ℝ) * a^3 * (c - b)^2 + (10/9 : ℝ) * a^2 * (b - a)^3 + (5/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (7/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (8/9 : ℝ) * a^2 * (c - b)^3 + (19/27 : ℝ) * a^1 * (b - a)^4 + (38/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (23/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (50/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (13/27 : ℝ) * a^1 * (c - b)^4 + (16/81 : ℝ) * (b - a)^5 + (40/81 : ℝ) * (b - a)^4 * (c - b)^1 + (76/81 : ℝ) * (b - a)^3 * (c - b)^2 + (74/81 : ℝ) * (b - a)^2 * (c - b)^3 + (32/81 : ℝ) * (b - a)^1 * (c - b)^4 + (5/81 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^5/81 + 7*a^4*b/81 + 7*a^4*c/81 - 4*a^3*b^2/81 - 26*a^3*b*c/81 - 4*a^3*c^2/81 - 4*a^2*b^3/81 + 5*a^2*b^2*c/27 + 5*a^2*b*c^2/27 - 4*a^2*c^3/81 + 7*a*b^4/81 - 26*a*b^3*c/81 + 5*a*b^2*c^2/27 - 26*a*b*c^3/81 + 7*a*c^4/81 + 5*b^5/81 + 7*b^4*c/81 - 4*b^3*c^2/81 - 4*b^2*c^3/81 + 7*b*c^4/81 + 5*c^5/81) := by
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
  have he : (a^2*b^2*c + a^2*b*c^2 + a*b^2*c^2 - 6*a*b - 6*a*c - 6*b*c + 15) = (5*a^5/81 + 7*a^4*b/81 + 7*a^4*c/81 - 4*a^3*b^2/81 - 26*a^3*b*c/81 - 4*a^3*c^2/81 - 4*a^2*b^3/81 + 5*a^2*b^2*c/27 + 5*a^2*b*c^2/27 - 4*a^2*c^3/81 + 7*a*b^4/81 - 26*a*b^3*c/81 + 5*a*b^2*c^2/27 - 26*a*b*c^3/81 + 7*a*c^4/81 + 5*b^5/81 + 7*b^4*c/81 - 4*b^3*c^2/81 - 4*b^2*c^3/81 + 7*b*c^4/81 + 5*c^5/81) := by
    linear_combination (-5*a^4/81 - 2*a^3*b/81 - 2*a^3*c/81 - 5*a^3/27 + 2*a^2*b^2/27 + 10*a^2*b*c/27 + a^2*b/9 + 2*a^2*c^2/27 + a^2*c/9 - 5*a^2/9 - 2*a*b^3/81 + 10*a*b^2*c/27 + a*b^2/9 + 10*a*b*c^2/27 + 8*a*b*c/9 + 8*a*b/9 - 2*a*c^3/81 + a*c^2/9 + 8*a*c/9 - 5*a/3 - 5*b^4/81 - 2*b^3*c/81 - 5*b^3/27 + 2*b^2*c^2/27 + b^2*c/9 - 5*b^2/9 - 2*b*c^3/81 + b*c^2/9 + 8*b*c/9 - 5*b/3 - 5*c^4/81 - 5*c^3/27 - 5*c^2/9 - 5*c/3 - 5) * habc
  have hn : 0 ≤ (a^2*b^2*c + a^2*b*c^2 + a*b^2*c^2 - 6*a*b - 6*a*c - 6*b*c + 15) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a * b * c + 15 / (a * b + b * c + c * a) ≥ 6) := @solution
#print axioms solution
