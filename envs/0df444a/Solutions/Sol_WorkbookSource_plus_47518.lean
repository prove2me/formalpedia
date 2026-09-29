-- Prove2me | solution 1 for WorkbookSource.plus_47518
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:25:06.990738+00:00
-- url     : https://prove2.me/submissions/a19fc4e7-aa26-42eb-8683-4ce003bbe017

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + 1) + b / (c + 1) + c / (a + 1)) ≥ 3 * (a + b + c) / (3 + a + b + c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^3*c + a^3 + a^2*b^2 - 2*a^2*b*c - a^2*b + a^2*c^2 + 2*a^2*c + a^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2 - 2*a*b*c^2 - 6*a*b*c - a*b - a*c^2 - a*c + b^3 + b^2*c^2 - b^2*c + b^2 + b*c^3 + 2*b*c^2 - b*c + c^3 + c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^2 * (b - a)^2 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (3 : ℝ) * a^2 * (c - b)^2 + (5 : ℝ) * a^1 * (b - a)^3 + (9 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (4 : ℝ) * a^1 * (b - a)^2 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^1 * (c - b)^3 + (4 : ℝ) * a^1 * (c - b)^2 + (2 : ℝ) * (b - a)^4 + (5 : ℝ) * (b - a)^3 * (c - b)^1 + (3 : ℝ) * (b - a)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^2 + (6 : ℝ) * (b - a)^2 * (c - b)^1 + (1 : ℝ) * (b - a)^2 + (1 : ℝ) * (b - a)^1 * (c - b)^3 + (5 : ℝ) * (b - a)^1 * (c - b)^2 + (1 : ℝ) * (b - a)^1 * (c - b)^1 + (1 : ℝ) * (c - b)^3 + (1 : ℝ) * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^3*c + a^3 + a^2*b^2 - 2*a^2*b*c - a^2*b + a^2*c^2 + 2*a^2*c + a^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2 - 2*a*b*c^2 - 6*a*b*c - a*b - a*c^2 - a*c + b^3 + b^2*c^2 - b^2*c + b^2 + b*c^3 + 2*b*c^2 - b*c + c^3 + c^2) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (3 : ℝ) * a^2 * (c - a)^2 + (3 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (3 : ℝ) * a^2 * (b - c)^2 + (5 : ℝ) * a^1 * (c - a)^3 + (6 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (4 : ℝ) * a^1 * (c - a)^2 + (3 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (4 : ℝ) * a^1 * (c - a)^1 * (b - c)^1 + (1 : ℝ) * a^1 * (b - c)^3 + (4 : ℝ) * a^1 * (b - c)^2 + (2 : ℝ) * (c - a)^4 + (3 : ℝ) * (c - a)^3 * (b - c)^1 + (3 : ℝ) * (c - a)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^2 + (3 : ℝ) * (c - a)^2 * (b - c)^1 + (1 : ℝ) * (c - a)^2 + (2 : ℝ) * (c - a)^1 * (b - c)^2 + (1 : ℝ) * (c - a)^1 * (b - c)^1 + (1 : ℝ) * (b - c)^3 + (1 : ℝ) * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^3*c + a^3 + a^2*b^2 - 2*a^2*b*c - a^2*b + a^2*c^2 + 2*a^2*c + a^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2 - 2*a*b*c^2 - 6*a*b*c - a*b - a*c^2 - a*c + b^3 + b^2*c^2 - b^2*c + b^2 + b*c^3 + 2*b*c^2 - b*c + c^3 + c^2) := by
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
  have hn : 0 ≤ (a^3*c + a^3 + a^2*b^2 - 2*a^2*b*c - a^2*b + a^2*c^2 + 2*a^2*c + a^2 + a*b^3 - 2*a*b^2*c + 2*a*b^2 - 2*a*b*c^2 - 6*a*b*c - a*b - a*c^2 - a*c + b^3 + b^2*c^2 - b^2*c + b^2 + b*c^3 + 2*b*c^2 - b*c + c^3 + c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + 1) + b / (c + 1) + c / (a + 1)) ≥ 3 * (a + b + c) / (3 + a + b + c)) := @solution
#print axioms solution
