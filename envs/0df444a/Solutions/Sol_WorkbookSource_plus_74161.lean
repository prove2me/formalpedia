-- Prove2me | solution 1 for WorkbookSource.plus_74161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:26.194115+00:00
-- url     : https://prove2.me/submissions/8c37a394-ef42-4195-8a1a-3f70e7625ce7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 1 ≥ a / (a + b) + b / (b + c) + c / (c + a) + 4 * a * b * c / ((a + b) * (b + c) * (c + a))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b + a^4*c + a^3*b*c + a^3*c^2 + a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 + a*b^4 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + a*c^4 + b^4*c + b^2*c^3 + b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * a^3 * (b - a)^2 + (11 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (11 : ℝ) * a^3 * (c - b)^2 + (23 : ℝ) * a^2 * (b - a)^3 + (36 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (33 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^2 * (c - b)^3 + (15 : ℝ) * a^1 * (b - a)^4 + (32 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (32 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (15 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^1 * (c - b)^4 + (3 : ℝ) * (b - a)^5 + (8 : ℝ) * (b - a)^4 * (c - b)^1 + (9 : ℝ) * (b - a)^3 * (c - b)^2 + (5 : ℝ) * (b - a)^2 * (c - b)^3 + (1 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b + a^4*c + a^3*b*c + a^3*c^2 + a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 + a*b^4 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + a*c^4 + b^4*c + b^2*c^3 + b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (11 : ℝ) * a^3 * (c - a)^2 + (11 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (11 : ℝ) * a^3 * (b - c)^2 + (23 : ℝ) * a^2 * (c - a)^3 + (33 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (30 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (10 : ℝ) * a^2 * (b - c)^3 + (15 : ℝ) * a^1 * (c - a)^4 + (28 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (26 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (13 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^1 * (b - c)^4 + (3 : ℝ) * (c - a)^5 + (7 : ℝ) * (c - a)^4 * (b - c)^1 + (7 : ℝ) * (c - a)^3 * (b - c)^2 + (4 : ℝ) * (c - a)^2 * (b - c)^3 + (1 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b + a^4*c + a^3*b*c + a^3*c^2 + a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 + a*b^4 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + a*c^4 + b^4*c + b^2*c^3 + b*c^4) := by
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
  have hn : 0 ≤ (a^4*b + a^4*c + a^3*b*c + a^3*c^2 + a^2*b^3 - 4*a^2*b^2*c - 4*a^2*b*c^2 + a*b^4 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + a*c^4 + b^4*c + b^2*c^3 + b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 1 ≥ a / (a + b) + b / (b + c) + c / (c + a) + 4 * a * b * c / ((a + b) * (b + c) * (c + a))) := @solution
#print axioms solution
