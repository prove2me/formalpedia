-- Prove2me | solution 1 for WorkbookSource.plus_20355
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:28:54.937832+00:00
-- url     : https://prove2.me/submissions/339f067f-8eef-4720-a9cd-e56d859b921a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + (128 * a * b * c) / (3 * (a + b + c)^3 + 47 * a * b * c) ≥ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^5 + 3*a^4*b + 3*a^4*c - 6*a^3*b^2 + 23*a^3*b*c - 6*a^3*c^2 - 6*a^2*b^3 - 20*a^2*b^2*c - 20*a^2*b*c^2 - 6*a^2*c^3 + 3*a*b^4 + 23*a*b^3*c - 20*a*b^2*c^2 + 23*a*b*c^3 + 3*a*c^4 + 3*b^5 + 3*b^4*c - 6*b^3*c^2 - 6*b^2*c^3 + 3*b*c^4 + 3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (47 : ℝ) * a^3 * (b - a)^2 + (47 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (47 : ℝ) * a^3 * (c - b)^2 + (76 : ℝ) * a^2 * (b - a)^3 + (114 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (168 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (65 : ℝ) * a^2 * (c - b)^3 + (32 : ℝ) * a^1 * (b - a)^4 + (64 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (139 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (107 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (21 : ℝ) * a^1 * (c - b)^4 + (24 : ℝ) * (b - a)^3 * (c - b)^2 + (36 : ℝ) * (b - a)^2 * (c - b)^3 + (18 : ℝ) * (b - a)^1 * (c - b)^4 + (3 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^5 + 3*a^4*b + 3*a^4*c - 6*a^3*b^2 + 23*a^3*b*c - 6*a^3*c^2 - 6*a^2*b^3 - 20*a^2*b^2*c - 20*a^2*b*c^2 - 6*a^2*c^3 + 3*a*b^4 + 23*a*b^3*c - 20*a*b^2*c^2 + 23*a*b*c^3 + 3*a*c^4 + 3*b^5 + 3*b^4*c - 6*b^3*c^2 - 6*b^2*c^3 + 3*b*c^4 + 3*c^5) := by
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
  have hn : 0 ≤ (3*a^5 + 3*a^4*b + 3*a^4*c - 6*a^3*b^2 + 23*a^3*b*c - 6*a^3*c^2 - 6*a^2*b^3 - 20*a^2*b^2*c - 20*a^2*b*c^2 - 6*a^2*c^3 + 3*a*b^4 + 23*a*b^3*c - 20*a*b^2*c^2 + 23*a*b*c^3 + 3*a*c^4 + 3*b^5 + 3*b^4*c - 6*b^3*c^2 - 6*b^2*c^3 + 3*b*c^4 + 3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + (128 * a * b * c) / (3 * (a + b + c)^3 + 47 * a * b * c) ≥ 2) := @solution
#print axioms solution
