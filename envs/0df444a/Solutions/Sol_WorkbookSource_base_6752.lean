-- Prove2me | solution 1 for WorkbookSource.base_6752
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:23:56.269151+00:00
-- url     : https://prove2.me/submissions/e60cfc10-962d-4520-b071-7989d3f80994

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * (b + c) / (b^2 + c^2) + b^2 * (c + a) / (c^2 + a^2) + c^2 * (a + b) / (a^2 + b^2)) ≥ a + b + c  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b + a^6*c - a^5*b^2 - a^5*c^2 - a^2*b^5 - a^2*c^5 + a*b^6 + a*c^6 + b^6*c - b^5*c^2 - b^2*c^5 + b*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^5 * (b - a)^2 + (8 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^5 * (c - b)^2 + (20 : ℝ) * a^4 * (b - a)^3 + (30 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (50 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (20 : ℝ) * a^4 * (c - b)^3 + (20 : ℝ) * a^3 * (b - a)^4 + (40 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (100 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (80 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (20 : ℝ) * a^3 * (c - b)^4 + (10 : ℝ) * a^2 * (b - a)^5 + (25 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (90 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (110 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (55 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^6 + (6 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (35 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (60 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (45 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^1 * (c - b)^6 + (4 : ℝ) * (b - a)^5 * (c - b)^2 + (10 : ℝ) * (b - a)^4 * (c - b)^3 + (10 : ℝ) * (b - a)^3 * (c - b)^4 + (5 : ℝ) * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^1 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b + a^6*c - a^5*b^2 - a^5*c^2 - a^2*b^5 - a^2*c^5 + a*b^6 + a*c^6 + b^6*c - b^5*c^2 - b^2*c^5 + b*c^6) := by
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
  have hn : 0 ≤ (a^6*b + a^6*c - a^5*b^2 - a^5*c^2 - a^2*b^5 - a^2*c^5 + a*b^6 + a*c^6 + b^6*c - b^5*c^2 - b^2*c^5 + b*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 * (b + c) / (b^2 + c^2) + b^2 * (c + a) / (c^2 + a^2) + c^2 * (a + b) / (a^2 + b^2)) ≥ a + b + c) := @solution
#print axioms solution
