-- Prove2me | solution 1 for WorkbookSource.plus_73378
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:24.683636+00:00
-- url     : https://prove2.me/submissions/4362ce4e-76e8-4cfc-ab3c-6456ee47bb33

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a + 3 * c) / (2 * a + b) + (5 * b + 3 * a) / (2 * b + c) + (5 * c + 3 * b) / (2 * c + a) ≥ 8   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^3 - 9*a^2*b + a^2*c + a*b^2 + 6*a*b*c - 9*a*c^2 + 6*b^3 - 9*b^2*c + b*c^2 + 6*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * a^1 * (b - a)^2 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (10 : ℝ) * a^1 * (c - b)^2 + (4 : ℝ) * (b - a)^3 + (11 : ℝ) * (b - a)^2 * (c - b)^1 + (19 : ℝ) * (b - a)^1 * (c - b)^2 + (6 : ℝ) * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (6*a^3 - 9*a^2*b + a^2*c + a*b^2 + 6*a*b*c - 9*a*c^2 + 6*b^3 - 9*b^2*c + b*c^2 + 6*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (10 : ℝ) * a^1 * (c - a)^2 + (10 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (10 : ℝ) * a^1 * (b - c)^2 + (4 : ℝ) * (c - a)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^1 + (9 : ℝ) * (c - a)^1 * (b - c)^2 + (6 : ℝ) * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^3 - 9*a^2*b + a^2*c + a*b^2 + 6*a*b*c - 9*a*c^2 + 6*b^3 - 9*b^2*c + b*c^2 + 6*c^3) := by
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
  have hn : 0 ≤ (6*a^3 - 9*a^2*b + a^2*c + a*b^2 + 6*a*b*c - 9*a*c^2 + 6*b^3 - 9*b^2*c + b*c^2 + 6*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (5 * a + 3 * c) / (2 * a + b) + (5 * b + 3 * a) / (2 * b + c) + (5 * c + 3 * b) / (2 * c + a) ≥ 8) := @solution
#print axioms solution
