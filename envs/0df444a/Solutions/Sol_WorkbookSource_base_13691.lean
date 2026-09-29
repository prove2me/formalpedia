-- Prove2me | solution 1 for WorkbookSource.base_13691
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:19.722483+00:00
-- url     : https://prove2.me/submissions/d2d0d06f-d1f9-42d5-8f84-b26942dea0a8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 + b^5 + c^5 ≥ a^2 * b^2 * c + a * b^2 * c^2 + a^2 * c^2 * b  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5 - a^2*b^2*c - a^2*b*c^2 - a*b^2*c^2 + b^5 + c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^3 * (b - a)^2 + (8 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^3 * (c - b)^2 + (14 : ℝ) * a^2 * (b - a)^3 + (21 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (27 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^2 * (c - b)^3 + (9 : ℝ) * a^1 * (b - a)^4 + (18 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (29 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (20 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (5 : ℝ) * a^1 * (c - b)^4 + (2 : ℝ) * (b - a)^5 + (5 : ℝ) * (b - a)^4 * (c - b)^1 + (10 : ℝ) * (b - a)^3 * (c - b)^2 + (10 : ℝ) * (b - a)^2 * (c - b)^3 + (5 : ℝ) * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5 - a^2*b^2*c - a^2*b*c^2 - a*b^2*c^2 + b^5 + c^5) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^5 + b^5 + c^5 ≥ a^2 * b^2 * c + a * b^2 * c^2 + a^2 * c^2 * b) := @solution
#print axioms solution
