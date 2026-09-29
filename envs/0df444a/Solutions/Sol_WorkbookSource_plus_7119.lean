-- Prove2me | solution 1 for WorkbookSource.plus_7119
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:44:31.327342+00:00
-- url     : https://prove2.me/submissions/13ccdf75-bf20-46a2-9d22-49424343b31c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (3 * a ^ 2 + b ^ 2 + 2 * c * a) + 2 * b / (3 * b ^ 2 + c ^ 2 + 2 * a * b) + 2 * c / (3 * c ^ 2 + a ^ 2 + 2 * b * c)) ≤ 3 / (a + b + c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^5*b + 11*a^4*b^2 - 14*a^4*b*c + 7*a^4*c^2 - 2*a^3*b^3 - 6*a^3*b^2*c - 2*a^3*b*c^2 - 2*a^3*c^3 + 7*a^2*b^4 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 6*a^2*b*c^3 + 11*a^2*c^4 - 14*a*b^4*c - 6*a*b^3*c^2 - 2*a*b^2*c^3 - 14*a*b*c^4 + 8*a*c^5 + 8*b^5*c + 11*b^4*c^2 - 2*b^3*c^3 + 7*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^4 * (b - a)^2 + (72 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (72 : ℝ) * a^4 * (c - b)^2 + (204 : ℝ) * a^3 * (b - a)^3 + (252 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (216 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (84 : ℝ) * a^3 * (c - b)^3 + (224 : ℝ) * a^2 * (b - a)^4 + (340 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (276 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (160 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (44 : ℝ) * a^2 * (c - b)^4 + (116 : ℝ) * a^1 * (b - a)^5 + (212 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (172 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (100 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (40 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * a^1 * (c - b)^5 + (24 : ℝ) * (b - a)^6 + (52 : ℝ) * (b - a)^5 * (c - b)^1 + (47 : ℝ) * (b - a)^4 * (c - b)^2 + (26 : ℝ) * (b - a)^3 * (c - b)^3 + (7 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (8*a^5*b + 11*a^4*b^2 - 14*a^4*b*c + 7*a^4*c^2 - 2*a^3*b^3 - 6*a^3*b^2*c - 2*a^3*b*c^2 - 2*a^3*c^3 + 7*a^2*b^4 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 6*a^2*b*c^3 + 11*a^2*c^4 - 14*a*b^4*c - 6*a*b^3*c^2 - 2*a*b^2*c^3 - 14*a*b*c^4 + 8*a*c^5 + 8*b^5*c + 11*b^4*c^2 - 2*b^3*c^3 + 7*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^4 * (c - a)^2 + (72 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (72 : ℝ) * a^4 * (b - c)^2 + (204 : ℝ) * a^3 * (c - a)^3 + (360 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (324 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (84 : ℝ) * a^3 * (b - c)^3 + (224 : ℝ) * a^2 * (c - a)^4 + (556 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (600 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (268 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (44 : ℝ) * a^2 * (b - c)^4 + (116 : ℝ) * a^1 * (c - a)^5 + (368 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (484 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (304 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (88 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (8 : ℝ) * a^1 * (b - c)^5 + (24 : ℝ) * (c - a)^6 + (92 : ℝ) * (c - a)^5 * (b - c)^1 + (147 : ℝ) * (c - a)^4 * (b - c)^2 + (122 : ℝ) * (c - a)^3 * (b - c)^3 + (51 : ℝ) * (c - a)^2 * (b - c)^4 + (8 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^5*b + 11*a^4*b^2 - 14*a^4*b*c + 7*a^4*c^2 - 2*a^3*b^3 - 6*a^3*b^2*c - 2*a^3*b*c^2 - 2*a^3*c^3 + 7*a^2*b^4 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 6*a^2*b*c^3 + 11*a^2*c^4 - 14*a*b^4*c - 6*a*b^3*c^2 - 2*a*b^2*c^3 - 14*a*b*c^4 + 8*a*c^5 + 8*b^5*c + 11*b^4*c^2 - 2*b^3*c^3 + 7*b^2*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (8*a^5*b + 11*a^4*b^2 - 14*a^4*b*c + 7*a^4*c^2 - 2*a^3*b^3 - 6*a^3*b^2*c - 2*a^3*b*c^2 - 2*a^3*c^3 + 7*a^2*b^4 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 6*a^2*b*c^3 + 11*a^2*c^4 - 14*a*b^4*c - 6*a*b^3*c^2 - 2*a*b^2*c^3 - 14*a*b*c^4 + 8*a*c^5 + 8*b^5*c + 11*b^4*c^2 - 2*b^3*c^3 + 7*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * a / (3 * a ^ 2 + b ^ 2 + 2 * c * a) + 2 * b / (3 * b ^ 2 + c ^ 2 + 2 * a * b) + 2 * c / (3 * c ^ 2 + a ^ 2 + 2 * b * c)) ≤ 3 / (a + b + c)) := @solution
#print axioms solution
