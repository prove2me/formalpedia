-- Prove2me | solution 1 for WorkbookSource.plus_20950
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:16.51903+00:00
-- url     : https://prove2.me/submissions/fa70eda4-a048-43fe-9a79-af69e088f930

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ 2 / 3 * (a / (a + b) + b / (b + c) + c / (c + a))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^4*b + 3*a^4*c - a^3*b^2 + a^3*c^2 + a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - a^2*c^3 + 3*a*b^4 - 6*a*b^2*c^2 + 3*a*c^4 + 3*b^4*c - b^3*c^2 + b^2*c^3 + 3*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^3 * (b - a)^2 + (24 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^3 * (c - b)^2 + (48 : ℝ) * a^2 * (b - a)^3 + (75 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (75 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (24 : ℝ) * a^2 * (c - b)^3 + (30 : ℝ) * a^1 * (b - a)^4 + (64 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (72 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (38 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^1 * (c - b)^4 + (6 : ℝ) * (b - a)^5 + (16 : ℝ) * (b - a)^4 * (c - b)^1 + (20 : ℝ) * (b - a)^3 * (c - b)^2 + (13 : ℝ) * (b - a)^2 * (c - b)^3 + (3 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^4*b + 3*a^4*c - a^3*b^2 + a^3*c^2 + a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - a^2*c^3 + 3*a*b^4 - 6*a*b^2*c^2 + 3*a*c^4 + 3*b^4*c - b^3*c^2 + b^2*c^3 + 3*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^3 * (c - a)^2 + (24 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (24 : ℝ) * a^3 * (b - c)^2 + (48 : ℝ) * a^2 * (c - a)^3 + (69 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (69 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (24 : ℝ) * a^2 * (b - c)^3 + (30 : ℝ) * a^1 * (c - a)^4 + (56 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (60 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (34 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (6 : ℝ) * a^1 * (b - c)^4 + (6 : ℝ) * (c - a)^5 + (14 : ℝ) * (c - a)^4 * (b - c)^1 + (16 : ℝ) * (c - a)^3 * (b - c)^2 + (11 : ℝ) * (c - a)^2 * (b - c)^3 + (3 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^4*b + 3*a^4*c - a^3*b^2 + a^3*c^2 + a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - a^2*c^3 + 3*a*b^4 - 6*a*b^2*c^2 + 3*a*c^4 + 3*b^4*c - b^3*c^2 + b^2*c^3 + 3*b*c^4) := by
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
  have hn : 0 ≤ (3*a^4*b + 3*a^4*c - a^3*b^2 + a^3*c^2 + a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - a^2*c^3 + 3*a*b^4 - 6*a*b^2*c^2 + 3*a*c^4 + 3*b^4*c - b^3*c^2 + b^2*c^3 + 3*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ 2 / 3 * (a / (a + b) + b / (b + c) + c / (c + a))) := @solution
#print axioms solution
