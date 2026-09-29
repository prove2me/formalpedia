-- Prove2me | solution 1 for WorkbookSource.base_2511
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:58:49.241433+00:00
-- url     : https://prove2.me/submissions/2575cb91-ac0e-40e9-b654-e5233c3f0bd5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 + b^5 + c^5) / (a * b * c) + 6 * (a * b + b * c + c * a) ≥ 7 * (a^2 + b^2 + c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 - 7*a^3*b*c + 6*a^2*b^2*c + 6*a^2*b*c^2 - 7*a*b^3*c + 6*a*b^2*c^2 - 7*a*b*c^3 + b^5 + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1 : ℝ) * a^3 * (b - a)^2 + (1 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^3 * (c - b)^2 + (6 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^2 * (c - b)^3 + (2 : ℝ) * a^1 * (b - a)^4 + (4 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (15 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (13 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (5 : ℝ) * a^1 * (c - b)^4 + (2 : ℝ) * (b - a)^5 + (5 : ℝ) * (b - a)^4 * (c - b)^1 + (10 : ℝ) * (b - a)^3 * (c - b)^2 + (10 : ℝ) * (b - a)^2 * (c - b)^3 + (5 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 - 7*a^3*b*c + 6*a^2*b^2*c + 6*a^2*b*c^2 - 7*a*b^3*c + 6*a*b^2*c^2 - 7*a*b*c^3 + b^5 + c^5) := by
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
  have hn : 0 ≤ (a^5 - 7*a^3*b*c + 6*a^2*b^2*c + 6*a^2*b*c^2 - 7*a*b^3*c + 6*a*b^2*c^2 - 7*a*b*c^3 + b^5 + c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^5 + b^5 + c^5) / (a * b * c) + 6 * (a * b + b * c + c * a) ≥ 7 * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
