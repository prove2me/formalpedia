-- Prove2me | solution 1 for WorkbookSource.base_39714
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:32.491577+00:00
-- url     : https://prove2.me/submissions/53be6fff-8de7-4ca9-b0be-a38093a7b3a1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + b^2 + c^2 + (9 * a * b * c * (a^2 + b^2 + c^2)) / (2 * (a^3 + b^3 + c^3) + 3 * a * b * c) ≥ 2 * (a * b + b * c + a * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 - 4*a^4*b - 4*a^4*c + 2*a^3*b^2 + 8*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 + 2*a^2*c^3 - 4*a*b^4 + 8*a*b^3*c - 6*a*b^2*c^2 + 8*a*b*c^3 - 4*a*c^4 + 2*b^5 - 4*b^4*c + 2*b^3*c^2 + 2*b^2*c^3 - 4*b*c^4 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^1 * (b - a)^4 + (4 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (6 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * (b - a)^3 * (c - b)^2 + (6 : ℝ) * (b - a)^2 * (c - b)^3 + (6 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 - 4*a^4*b - 4*a^4*c + 2*a^3*b^2 + 8*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 + 2*a^2*c^3 - 4*a*b^4 + 8*a*b^3*c - 6*a*b^2*c^2 + 8*a*b*c^3 - 4*a*c^4 + 2*b^5 - 4*b^4*c + 2*b^3*c^2 + 2*b^2*c^3 - 4*b*c^4 + 2*c^5) := by
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
  have hn : 0 ≤ (2*(a^2 - a*b - a*c + b^2 - b*c + c^2)*(a^3 - a^2*b - a^2*c - a*b^2 + 3*a*b*c - a*c^2 + b^3 - b^2*c - b*c^2 + c^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^2 + b^2 + c^2 + (9 * a * b * c * (a^2 + b^2 + c^2)) / (2 * (a^3 + b^3 + c^3) + 3 * a * b * c) ≥ 2 * (a * b + b * c + a * c)) := @solution
#print axioms solution
