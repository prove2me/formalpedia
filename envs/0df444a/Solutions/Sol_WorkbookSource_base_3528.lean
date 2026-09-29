-- Prove2me | solution 1 for WorkbookSource.base_3528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:09:17.968262+00:00
-- url     : https://prove2.me/submissions/84447ab8-76d6-4284-ac92-9af1cf0365b8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) / (a ^ 2 + (b + c) ^ 2) + b * (c + a) / (b ^ 2 + (c + a) ^ 2) + c * (a + b) / (c ^ 2 + (a + b) ^ 2)) ≤ 6 / 5  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^6 + 2*a^5*b + 2*a^5*c - 2*a^4*b^2 + 6*a^4*b*c - 2*a^4*c^2 + 4*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 4*a^3*c^3 - 2*a^2*b^4 - 12*a^2*b^3*c + 24*a^2*b^2*c^2 - 12*a^2*b*c^3 - 2*a^2*c^4 + 2*a*b^5 + 6*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 + 6*a*b*c^4 + 2*a*c^5 + 6*b^6 + 2*b^5*c - 2*b^4*c^2 + 4*b^3*c^3 - 2*b^2*c^4 + 2*b*c^5 + 6*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (90 : ℝ) * a^4 * (b - a)^2 + (90 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (90 : ℝ) * a^4 * (c - b)^2 + (208 : ℝ) * a^3 * (b - a)^3 + (312 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (408 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (152 : ℝ) * a^3 * (c - b)^3 + (196 : ℝ) * a^2 * (b - a)^4 + (392 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (648 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (452 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (112 : ℝ) * a^2 * (c - b)^4 + (88 : ℝ) * a^1 * (b - a)^5 + (220 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (440 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (440 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (212 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (40 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (48 : ℝ) * (b - a)^5 * (c - b)^1 + (108 : ℝ) * (b - a)^4 * (c - b)^2 + (136 : ℝ) * (b - a)^3 * (c - b)^3 + (98 : ℝ) * (b - a)^2 * (c - b)^4 + (38 : ℝ) * (b - a)^1 * (c - b)^5 + (6 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^6 + 2*a^5*b + 2*a^5*c - 2*a^4*b^2 + 6*a^4*b*c - 2*a^4*c^2 + 4*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 4*a^3*c^3 - 2*a^2*b^4 - 12*a^2*b^3*c + 24*a^2*b^2*c^2 - 12*a^2*b*c^3 - 2*a^2*c^4 + 2*a*b^5 + 6*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 + 6*a*b*c^4 + 2*a*c^5 + 6*b^6 + 2*b^5*c - 2*b^4*c^2 + 4*b^3*c^3 - 2*b^2*c^4 + 2*b*c^5 + 6*c^6) := by
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
  have hn : 0 ≤ (6*a^6 + 2*a^5*b + 2*a^5*c - 2*a^4*b^2 + 6*a^4*b*c - 2*a^4*c^2 + 4*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 4*a^3*c^3 - 2*a^2*b^4 - 12*a^2*b^3*c + 24*a^2*b^2*c^2 - 12*a^2*b*c^3 - 2*a^2*c^4 + 2*a*b^5 + 6*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 + 6*a*b*c^4 + 2*a*c^5 + 6*b^6 + 2*b^5*c - 2*b^4*c^2 + 4*b^3*c^3 - 2*b^2*c^4 + 2*b*c^5 + 6*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * (b + c) / (a ^ 2 + (b + c) ^ 2) + b * (c + a) / (b ^ 2 + (c + a) ^ 2) + c * (a + b) / (c ^ 2 + (a + b) ^ 2)) ≤ 6 / 5) := @solution
#print axioms solution
