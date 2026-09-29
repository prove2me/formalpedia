-- Prove2me | solution 1 for WorkbookSource.plus_53138
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:21.207661+00:00
-- url     : https://prove2.me/submissions/c2646112-32f2-4bcb-8cf4-e27d36b68108

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  6 * (1 / a + 1 / b + 1 / c) * (a + b + c) ^ 3 + 3 * (a * b + b * c + c * a) ≥ 55 * (a + b + c) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^4*b + 6*a^4*c + 18*a^3*b^2 - 13*a^3*b*c + 18*a^3*c^2 + 18*a^2*b^3 - 35*a^2*b^2*c - 35*a^2*b*c^2 + 18*a^2*c^3 + 6*a*b^4 - 13*a*b^3*c - 35*a*b^2*c^2 - 13*a*b*c^3 + 6*a*c^4 + 6*b^4*c + 18*b^3*c^2 + 18*b^2*c^3 + 6*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (107 : ℝ) * a^3 * (b - a)^2 + (107 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (107 : ℝ) * a^3 * (c - b)^2 + (250 : ℝ) * a^2 * (b - a)^3 + (375 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (267 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (71 : ℝ) * a^2 * (c - b)^3 + (191 : ℝ) * a^1 * (b - a)^4 + (382 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (286 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (95 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^1 * (c - b)^4 + (48 : ℝ) * (b - a)^5 + (120 : ℝ) * (b - a)^4 * (c - b)^1 + (108 : ℝ) * (b - a)^3 * (c - b)^2 + (42 : ℝ) * (b - a)^2 * (c - b)^3 + (6 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^4*b + 6*a^4*c + 18*a^3*b^2 - 13*a^3*b*c + 18*a^3*c^2 + 18*a^2*b^3 - 35*a^2*b^2*c - 35*a^2*b*c^2 + 18*a^2*c^3 + 6*a*b^4 - 13*a*b^3*c - 35*a*b^2*c^2 - 13*a*b*c^3 + 6*a*c^4 + 6*b^4*c + 18*b^3*c^2 + 18*b^2*c^3 + 6*b*c^4) := by
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
  have hn : 0 ≤ (6*a^4*b + 6*a^4*c + 18*a^3*b^2 - 13*a^3*b*c + 18*a^3*c^2 + 18*a^2*b^3 - 35*a^2*b^2*c - 35*a^2*b*c^2 + 18*a^2*c^3 + 6*a*b^4 - 13*a*b^3*c - 35*a*b^2*c^2 - 13*a*b*c^3 + 6*a*c^4 + 6*b^4*c + 18*b^3*c^2 + 18*b^2*c^3 + 6*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 6 * (1 / a + 1 / b + 1 / c) * (a + b + c) ^ 3 + 3 * (a * b + b * c + c * a) ≥ 55 * (a + b + c) ^ 2) := @solution
#print axioms solution
