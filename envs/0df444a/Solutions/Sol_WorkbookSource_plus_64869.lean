-- Prove2me | solution 1 for WorkbookSource.plus_64869
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:42:31.702908+00:00
-- url     : https://prove2.me/submissions/de85eaae-0f77-4328-8c90-1cf578d9e068

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a ^ 3 + 2 * b ^ 3) / (a ^ 2 + b ^ 2) + (3 * b ^ 3 + 2 * c ^ 3) / (b ^ 2 + c ^ 2) + (3 * c ^ 3 + 2 * a ^ 3) / (c ^ 2 + a ^ 2) ≥ 5 / 2 * (a + b + c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^5*b^2 + 5*a^5*c^2 + a^4*b^3 - 5*a^4*b^2*c - 5*a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^3*c^4 + 5*a^2*b^5 - 5*a^2*b^4*c - 5*a^2*b*c^4 + 5*a^2*c^5 - 5*a*b^4*c^2 - 5*a*b^2*c^4 + 5*b^5*c^2 + b^4*c^3 - b^3*c^4 + 5*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^5 * (b - a)^2 + (40 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (40 : ℝ) * a^5 * (c - b)^2 + (140 : ℝ) * a^4 * (b - a)^3 + (204 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (184 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (60 : ℝ) * a^4 * (c - b)^3 + (200 : ℝ) * a^3 * (b - a)^4 + (384 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (376 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (192 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (40 : ℝ) * a^3 * (c - b)^4 + (150 : ℝ) * a^2 * (b - a)^5 + (360 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (400 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (252 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (82 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^2 * (c - b)^5 + (60 : ℝ) * a^1 * (b - a)^6 + (174 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (225 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (168 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (67 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (10 : ℝ) * (b - a)^7 + (34 : ℝ) * (b - a)^6 * (c - b)^1 + (52 : ℝ) * (b - a)^5 * (c - b)^2 + (47 : ℝ) * (b - a)^4 * (c - b)^3 + (24 : ℝ) * (b - a)^3 * (c - b)^4 + (5 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (5*a^5*b^2 + 5*a^5*c^2 + a^4*b^3 - 5*a^4*b^2*c - 5*a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^3*c^4 + 5*a^2*b^5 - 5*a^2*b^4*c - 5*a^2*b*c^4 + 5*a^2*c^5 - 5*a*b^4*c^2 - 5*a*b^2*c^4 + 5*b^5*c^2 + b^4*c^3 - b^3*c^4 + 5*b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^5 * (c - a)^2 + (40 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (40 : ℝ) * a^5 * (b - c)^2 + (140 : ℝ) * a^4 * (c - a)^3 + (216 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (196 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (60 : ℝ) * a^4 * (b - c)^3 + (200 : ℝ) * a^3 * (c - a)^4 + (416 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (424 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (208 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (40 : ℝ) * a^3 * (b - c)^4 + (150 : ℝ) * a^2 * (c - a)^5 + (390 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (460 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (288 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (88 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (10 : ℝ) * a^2 * (b - c)^5 + (60 : ℝ) * a^1 * (c - a)^6 + (186 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (255 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (192 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (73 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (10 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (10 : ℝ) * (c - a)^7 + (36 : ℝ) * (c - a)^6 * (b - c)^1 + (58 : ℝ) * (c - a)^5 * (b - c)^2 + (53 : ℝ) * (c - a)^4 * (b - c)^3 + (26 : ℝ) * (c - a)^3 * (b - c)^4 + (5 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^5*b^2 + 5*a^5*c^2 + a^4*b^3 - 5*a^4*b^2*c - 5*a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^3*c^4 + 5*a^2*b^5 - 5*a^2*b^4*c - 5*a^2*b*c^4 + 5*a^2*c^5 - 5*a*b^4*c^2 - 5*a*b^2*c^4 + 5*b^5*c^2 + b^4*c^3 - b^3*c^4 + 5*b^2*c^5) := by
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
  have hn : 0 ≤ (5*a^5*b^2 + 5*a^5*c^2 + a^4*b^3 - 5*a^4*b^2*c - 5*a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^3*c^4 + 5*a^2*b^5 - 5*a^2*b^4*c - 5*a^2*b*c^4 + 5*a^2*c^5 - 5*a*b^4*c^2 - 5*a*b^2*c^4 + 5*b^5*c^2 + b^4*c^3 - b^3*c^4 + 5*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * a ^ 3 + 2 * b ^ 3) / (a ^ 2 + b ^ 2) + (3 * b ^ 3 + 2 * c ^ 3) / (b ^ 2 + c ^ 2) + (3 * c ^ 3 + 2 * a ^ 3) / (c ^ 2 + a ^ 2) ≥ 5 / 2 * (a + b + c)) := @solution
#print axioms solution
