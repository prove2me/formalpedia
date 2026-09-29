-- Prove2me | solution 1 for WorkbookSource.base_37591
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:39.311191+00:00
-- url     : https://prove2.me/submissions/7217a3cb-aab3-4146-b2f9-b96e853dab8d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) + a * b * c / (6 * (a ^ 3 + b ^ 3 + c ^ 3)) ≥ 19 / 18  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (18*a^6 - 13*a^5*b - 13*a^5*c - 13*a^4*b^2 - 8*a^4*b*c - 13*a^4*c^2 + 36*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 36*a^3*c^3 - 13*a^2*b^4 - a^2*b^3*c + 24*a^2*b^2*c^2 - a^2*b*c^3 - 13*a^2*c^4 - 13*a*b^5 - 8*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 - 8*a*b*c^4 - 13*a*c^5 + 18*b^6 - 13*b^5*c - 13*b^4*c^2 + 36*b^3*c^3 - 13*b^2*c^4 - 13*b*c^5 + 18*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (14 : ℝ) * a^3 * (b - a)^3 + (21 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (75 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (34 : ℝ) * a^3 * (c - b)^3 + (76 : ℝ) * a^2 * (b - a)^4 + (152 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (339 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (263 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (106 : ℝ) * a^2 * (c - b)^4 + (76 : ℝ) * a^1 * (b - a)^5 + (190 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (446 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (479 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (311 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (82 : ℝ) * a^1 * (c - b)^5 + (20 : ℝ) * (b - a)^6 + (60 : ℝ) * (b - a)^5 * (c - b)^1 + (157 : ℝ) * (b - a)^4 * (c - b)^2 + (214 : ℝ) * (b - a)^3 * (c - b)^3 + (192 : ℝ) * (b - a)^2 * (c - b)^4 + (95 : ℝ) * (b - a)^1 * (c - b)^5 + (18 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (18*a^6 - 13*a^5*b - 13*a^5*c - 13*a^4*b^2 - 8*a^4*b*c - 13*a^4*c^2 + 36*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 36*a^3*c^3 - 13*a^2*b^4 - a^2*b^3*c + 24*a^2*b^2*c^2 - a^2*b*c^3 - 13*a^2*c^4 - 13*a*b^5 - 8*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 - 8*a*b*c^4 - 13*a*c^5 + 18*b^6 - 13*b^5*c - 13*b^4*c^2 + 36*b^3*c^3 - 13*b^2*c^4 - 13*b*c^5 + 18*c^6) := by
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
  have hn : 0 ≤ (18*a^6 - 13*a^5*b - 13*a^5*c - 13*a^4*b^2 - 8*a^4*b*c - 13*a^4*c^2 + 36*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 + 36*a^3*c^3 - 13*a^2*b^4 - a^2*b^3*c + 24*a^2*b^2*c^2 - a^2*b*c^3 - 13*a^2*c^4 - 13*a*b^5 - 8*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 - 8*a*b*c^4 - 13*a*c^5 + 18*b^6 - 13*b^5*c - 13*b^4*c^2 + 36*b^3*c^3 - 13*b^2*c^4 - 13*b*c^5 + 18*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) + a * b * c / (6 * (a ^ 3 + b ^ 3 + c ^ 3)) ≥ 19 / 18) := @solution
#print axioms solution
