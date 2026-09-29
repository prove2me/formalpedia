-- Prove2me | solution 1 for WorkbookSource.base_13753
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:20.632903+00:00
-- url     : https://prove2.me/submissions/c6873e79-d941-4df4-bae2-f4a0d6c8b702

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (a + b - c) * (b + c - a) * (c + a - b) ≤ a * b * c * (a * b + b * c + a * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 - a^4*b - a^4*c + 2*a^3*b*c - a^2*b^2*c - a^2*b*c^2 - a*b^4 + 2*a*b^3*c - a*b^2*c^2 + 2*a*b*c^3 - a*c^4 + b^5 - b^4*c - b*c^4 + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^3 * (b - a)^2 + (2 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^3 * (c - b)^2 + (2 : ℝ) * a^2 * (b - a)^3 + (3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (9 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^2 * (c - b)^3 + (1 : ℝ) * a^1 * (b - a)^4 + (2 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (11 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (10 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (3 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * (b - a)^3 * (c - b)^2 + (6 : ℝ) * (b - a)^2 * (c - b)^3 + (4 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 - a^4*b - a^4*c + 2*a^3*b*c - a^2*b^2*c - a^2*b*c^2 - a*b^4 + 2*a*b^3*c - a*b^2*c^2 + 2*a*b*c^3 - a*c^4 + b^5 - b^4*c - b*c^4 + c^5) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) * (a + b - c) * (b + c - a) * (c + a - b) ≤ a * b * c * (a * b + b * c + a * c)) := @solution
#print axioms solution
