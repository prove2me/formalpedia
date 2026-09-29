-- Prove2me | solution 1 for WorkbookSource.plus_61932
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:40:22.243299+00:00
-- url     : https://prove2.me/submissions/349d7d12-7e38-4d55-a4e6-af733a7571c5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (23 / (8 * b ^ 2 + 7 * b * c + 8 * c ^ 2) + 23 / (8 * c ^ 2 + 7 * c * a + 8 * a ^ 2) + 23 / (8 * a ^ 2 + 7 * a * b + 8 * b ^ 2)) ≥ 27 / (a + b + c) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (1472*a^6 + 4232*a^5*b + 4232*a^5*c - 5360*a^4*b^2 - 297*a^4*b*c - 5360*a^4*c^2 - 688*a^3*b^3 + 1125*a^3*b^2*c + 1125*a^3*b*c^2 - 688*a^3*c^3 - 5360*a^2*b^4 + 1125*a^2*b^3*c - 1443*a^2*b^2*c^2 + 1125*a^2*b*c^3 - 5360*a^2*c^4 + 4232*a*b^5 - 297*a*b^4*c + 1125*a*b^3*c^2 + 1125*a*b^2*c^3 - 297*a*b*c^4 + 4232*a*c^5 + 1472*b^6 + 4232*b^5*c - 5360*b^4*c^2 - 688*b^3*c^3 - 5360*b^2*c^4 + 4232*b*c^5 + 1472*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (33327 : ℝ) * a^4 * (b - a)^2 + (33327 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (33327 : ℝ) * a^4 * (c - b)^2 + (62422 : ℝ) * a^3 * (b - a)^3 + (93633 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (172983 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (70886 : ℝ) * a^3 * (c - b)^3 + (40687 : ℝ) * a^2 * (b - a)^4 + (81374 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (253782 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (213095 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (53383 : ℝ) * a^2 * (c - b)^4 + (10120 : ℝ) * a^1 * (b - a)^5 + (25300 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (144302 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (191153 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (96623 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (17296 : ℝ) * a^1 * (c - b)^5 + (24816 : ℝ) * (b - a)^4 * (c - b)^2 + (49632 : ℝ) * (b - a)^3 * (c - b)^3 + (37880 : ℝ) * (b - a)^2 * (c - b)^4 + (13064 : ℝ) * (b - a)^1 * (c - b)^5 + (1472 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (1472*a^6 + 4232*a^5*b + 4232*a^5*c - 5360*a^4*b^2 - 297*a^4*b*c - 5360*a^4*c^2 - 688*a^3*b^3 + 1125*a^3*b^2*c + 1125*a^3*b*c^2 - 688*a^3*c^3 - 5360*a^2*b^4 + 1125*a^2*b^3*c - 1443*a^2*b^2*c^2 + 1125*a^2*b*c^3 - 5360*a^2*c^4 + 4232*a*b^5 - 297*a*b^4*c + 1125*a*b^3*c^2 + 1125*a*b^2*c^3 - 297*a*b*c^4 + 4232*a*c^5 + 1472*b^6 + 4232*b^5*c - 5360*b^4*c^2 - 688*b^3*c^3 - 5360*b^2*c^4 + 4232*b*c^5 + 1472*c^6) := by
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
  have hn : 0 ≤ (1472*a^6 + 4232*a^5*b + 4232*a^5*c - 5360*a^4*b^2 - 297*a^4*b*c - 5360*a^4*c^2 - 688*a^3*b^3 + 1125*a^3*b^2*c + 1125*a^3*b*c^2 - 688*a^3*c^3 - 5360*a^2*b^4 + 1125*a^2*b^3*c - 1443*a^2*b^2*c^2 + 1125*a^2*b*c^3 - 5360*a^2*c^4 + 4232*a*b^5 - 297*a*b^4*c + 1125*a*b^3*c^2 + 1125*a*b^2*c^3 - 297*a*b*c^4 + 4232*a*c^5 + 1472*b^6 + 4232*b^5*c - 5360*b^4*c^2 - 688*b^3*c^3 - 5360*b^2*c^4 + 4232*b*c^5 + 1472*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (23 / (8 * b ^ 2 + 7 * b * c + 8 * c ^ 2) + 23 / (8 * c ^ 2 + 7 * c * a + 8 * a ^ 2) + 23 / (8 * a ^ 2 + 7 * a * b + 8 * b ^ 2)) ≥ 27 / (a + b + c) ^ 2) := @solution
#print axioms solution
