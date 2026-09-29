-- Prove2me | solution 1 for WorkbookSource.base_38183
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:39:47.973806+00:00
-- url     : https://prove2.me/submissions/d3dd8551-4bf1-4f63-b493-7dac04c6f6de

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a + b + c)) / (2 * (a * b + b * c + c * a)) ≥ a / (a ^ 2 + b ^ 2) + b / (b ^ 2 + c ^ 2) + c / (c ^ 2 + a ^ 2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b^2 - 2*a^5*b*c + 3*a^5*c^2 + a^4*b^3 - a^4*b^2*c + a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 6*a^3*b^3*c + 2*a^3*b^2*c^2 - 6*a^3*b*c^3 + a^3*c^4 + 3*a^2*b^5 + a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 + a^2*c^5 - 2*a*b^5*c - a*b^4*c^2 - 6*a*b^3*c^3 + a*b^2*c^4 - 2*a*b*c^5 + b^5*c^2 + b^4*c^3 + b^3*c^4 + 3*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^5 * (b - a)^2 + (16 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^5 * (c - b)^2 + (60 : ℝ) * a^4 * (b - a)^3 + (108 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (88 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (20 : ℝ) * a^4 * (c - b)^3 + (92 : ℝ) * a^3 * (b - a)^4 + (232 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (228 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (88 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^3 * (c - b)^4 + (74 : ℝ) * a^2 * (b - a)^5 + (232 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (280 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (152 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (34 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^2 * (c - b)^5 + (32 : ℝ) * a^1 * (b - a)^6 + (116 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (167 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (118 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (39 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (6 : ℝ) * (b - a)^7 + (24 : ℝ) * (b - a)^6 * (c - b)^1 + (40 : ℝ) * (b - a)^5 * (c - b)^2 + (35 : ℝ) * (b - a)^4 * (c - b)^3 + (16 : ℝ) * (b - a)^3 * (c - b)^4 + (3 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b^2 - 2*a^5*b*c + 3*a^5*c^2 + a^4*b^3 - a^4*b^2*c + a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 6*a^3*b^3*c + 2*a^3*b^2*c^2 - 6*a^3*b*c^3 + a^3*c^4 + 3*a^2*b^5 + a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 + a^2*c^5 - 2*a*b^5*c - a*b^4*c^2 - 6*a*b^3*c^3 + a*b^2*c^4 - 2*a*b*c^5 + b^5*c^2 + b^4*c^3 + b^3*c^4 + 3*b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^5 * (c - a)^2 + (16 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (16 : ℝ) * a^5 * (b - c)^2 + (60 : ℝ) * a^4 * (c - a)^3 + (72 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (52 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (20 : ℝ) * a^4 * (b - c)^3 + (92 : ℝ) * a^3 * (c - a)^4 + (136 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (84 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (40 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (12 : ℝ) * a^3 * (b - c)^4 + (74 : ℝ) * a^2 * (c - a)^5 + (138 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (92 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (36 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (12 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^2 * (b - c)^5 + (32 : ℝ) * a^1 * (c - a)^6 + (76 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (67 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (30 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (7 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (6 : ℝ) * (c - a)^7 + (18 : ℝ) * (c - a)^6 * (b - c)^1 + (22 : ℝ) * (c - a)^5 * (b - c)^2 + (15 : ℝ) * (c - a)^4 * (b - c)^3 + (6 : ℝ) * (c - a)^3 * (b - c)^4 + (1 : ℝ) * (c - a)^2 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b^2 - 2*a^5*b*c + 3*a^5*c^2 + a^4*b^3 - a^4*b^2*c + a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 6*a^3*b^3*c + 2*a^3*b^2*c^2 - 6*a^3*b*c^3 + a^3*c^4 + 3*a^2*b^5 + a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 + a^2*c^5 - 2*a*b^5*c - a*b^4*c^2 - 6*a*b^3*c^3 + a*b^2*c^4 - 2*a*b*c^5 + b^5*c^2 + b^4*c^3 + b^3*c^4 + 3*b^2*c^5) := by
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
  have hn : 0 ≤ (a^5*b^2 - 2*a^5*b*c + 3*a^5*c^2 + a^4*b^3 - a^4*b^2*c + a^4*b*c^2 + a^4*c^3 + a^3*b^4 - 6*a^3*b^3*c + 2*a^3*b^2*c^2 - 6*a^3*b*c^3 + a^3*c^4 + 3*a^2*b^5 + a^2*b^4*c + 2*a^2*b^3*c^2 + 2*a^2*b^2*c^3 - a^2*b*c^4 + a^2*c^5 - 2*a*b^5*c - a*b^4*c^2 - 6*a*b^3*c^3 + a*b^2*c^4 - 2*a*b*c^5 + b^5*c^2 + b^4*c^3 + b^3*c^4 + 3*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * (a + b + c)) / (2 * (a * b + b * c + c * a)) ≥ a / (a ^ 2 + b ^ 2) + b / (b ^ 2 + c ^ 2) + c / (c ^ 2 + a ^ 2)) := @solution
#print axioms solution
