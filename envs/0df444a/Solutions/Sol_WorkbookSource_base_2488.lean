-- Prove2me | solution 1 for WorkbookSource.base_2488
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:58:48.548313+00:00
-- url     : https://prove2.me/submissions/3d8f430f-350c-4ef1-bbde-f7ceebf085fc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b) / (c * (c + a)) + (b * c) / (a * (a + b)) + (c * a) / (b * (b + c)) ≥ a / (c + a) + b / (a + b) + c / (b + c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*c^2 + a^3*b^3 - a^3*b*c^2 + a^3*c^3 + a^2*b^4 - a^2*b^3*c - 3*a^2*b^2*c^2 - a*b^2*c^3 + b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^4 * (b - a)^2 + (6 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^4 * (c - b)^2 + (19 : ℝ) * a^3 * (b - a)^3 + (32 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (23 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (5 : ℝ) * a^3 * (c - b)^3 + (22 : ℝ) * a^2 * (b - a)^4 + (51 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (42 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (13 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^2 * (c - b)^4 + (11 : ℝ) * a^1 * (b - a)^5 + (32 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (33 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (14 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (b - a)^6 + (7 : ℝ) * (b - a)^5 * (c - b)^1 + (9 : ℝ) * (b - a)^4 * (c - b)^2 + (5 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*c^2 + a^3*b^3 - a^3*b*c^2 + a^3*c^3 + a^2*b^4 - a^2*b^3*c - 3*a^2*b^2*c^2 - a*b^2*c^3 + b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^4 * (c - a)^2 + (6 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (6 : ℝ) * a^4 * (b - c)^2 + (19 : ℝ) * a^3 * (c - a)^3 + (25 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (16 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (5 : ℝ) * a^3 * (b - c)^3 + (22 : ℝ) * a^2 * (c - a)^4 + (37 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (21 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (6 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^2 * (b - c)^4 + (11 : ℝ) * a^1 * (c - a)^5 + (23 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (15 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (3 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (2 : ℝ) * (c - a)^6 + (5 : ℝ) * (c - a)^5 * (b - c)^1 + (4 : ℝ) * (c - a)^4 * (b - c)^2 + (1 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*c^2 + a^3*b^3 - a^3*b*c^2 + a^3*c^3 + a^2*b^4 - a^2*b^3*c - 3*a^2*b^2*c^2 - a*b^2*c^3 + b^3*c^3 + b^2*c^4) := by
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
  have hn : 0 ≤ (a^4*c^2 + a^3*b^3 - a^3*b*c^2 + a^3*c^3 + a^2*b^4 - a^2*b^3*c - 3*a^2*b^2*c^2 - a*b^2*c^3 + b^3*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b) / (c * (c + a)) + (b * c) / (a * (a + b)) + (c * a) / (b * (b + c)) ≥ a / (c + a) + b / (a + b) + c / (b + c)) := @solution
#print axioms solution
