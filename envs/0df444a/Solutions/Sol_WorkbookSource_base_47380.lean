-- Prove2me | solution 1 for WorkbookSource.base_47380
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:14:24.622052+00:00
-- url     : https://prove2.me/submissions/0d1b885f-64f7-48f8-8291-c3c90f6955d1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a + 4 * b + c + 2) / (4 * b + c + 1) + (5 * b + 4 * c + a + 2) / (4 * c + a + 1) + (5 * c + 4 * a + b + 2) / (4 * a + b + 1) ≥ 6  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (20*a^3 - 43*a^2*b + 68*a^2*c + 17*a^2 + 68*a*b^2 - 135*a*b*c - 17*a*b - 43*a*c^2 - 17*a*c + 20*b^3 - 43*b^2*c + 17*b^2 + 68*b*c^2 - 17*b*c + 20*c^3 + 17*c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (85 : ℝ) * a^1 * (b - a)^2 + (85 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (85 : ℝ) * a^1 * (c - b)^2 + (65 : ℝ) * (b - a)^3 + (153 : ℝ) * (b - a)^2 * (c - b)^1 + (17 : ℝ) * (b - a)^2 + (128 : ℝ) * (b - a)^1 * (c - b)^2 + (17 : ℝ) * (b - a)^1 * (c - b)^1 + (20 : ℝ) * (c - b)^3 + (17 : ℝ) * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (20*a^3 - 43*a^2*b + 68*a^2*c + 17*a^2 + 68*a*b^2 - 135*a*b*c - 17*a*b - 43*a*c^2 - 17*a*c + 20*b^3 - 43*b^2*c + 17*b^2 + 68*b*c^2 - 17*b*c + 20*c^3 + 17*c^2) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (85 : ℝ) * a^1 * (c - a)^2 + (85 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (85 : ℝ) * a^1 * (b - c)^2 + (65 : ℝ) * (c - a)^3 + (42 : ℝ) * (c - a)^2 * (b - c)^1 + (17 : ℝ) * (c - a)^2 + (17 : ℝ) * (c - a)^1 * (b - c)^2 + (17 : ℝ) * (c - a)^1 * (b - c)^1 + (20 : ℝ) * (b - c)^3 + (17 : ℝ) * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (20*a^3 - 43*a^2*b + 68*a^2*c + 17*a^2 + 68*a*b^2 - 135*a*b*c - 17*a*b - 43*a*c^2 - 17*a*c + 20*b^3 - 43*b^2*c + 17*b^2 + 68*b*c^2 - 17*b*c + 20*c^3 + 17*c^2) := by
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
  have hn : 0 ≤ (20*a^3 - 43*a^2*b + 68*a^2*c + 17*a^2 + 68*a*b^2 - 135*a*b*c - 17*a*b - 43*a*c^2 - 17*a*c + 20*b^3 - 43*b^2*c + 17*b^2 + 68*b*c^2 - 17*b*c + 20*c^3 + 17*c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (5 * a + 4 * b + c + 2) / (4 * b + c + 1) + (5 * b + 4 * c + a + 2) / (4 * c + a + 1) + (5 * c + 4 * a + b + 2) / (4 * a + b + 1) ≥ 6) := @solution
#print axioms solution
