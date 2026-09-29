-- Prove2me | solution 1 for WorkbookSource.base_47396
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:14:25.292885+00:00
-- url     : https://prove2.me/submissions/052d6e8e-5981-469b-ac1e-127483aee8c9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * (a + 2 * c) / (3 * b) + b^2 * (b + 2 * a) / (3 * c) + c^2 * (c + 2 * b) / (3 * a) ≥ a^2 + b^2 + c^2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*c - 3*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 + a*b^4 - 3*a*b^3*c - 3*a*b*c^3 + 2*b^2*c^3 + b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * a^3 * (b - a)^2 + (5 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (5 : ℝ) * a^3 * (c - b)^2 + (12 : ℝ) * a^2 * (b - a)^3 + (24 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (18 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^2 * (c - b)^3 + (10 : ℝ) * a^1 * (b - a)^4 + (28 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (27 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (9 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (1 : ℝ) * a^1 * (c - b)^4 + (3 : ℝ) * (b - a)^5 + (10 : ℝ) * (b - a)^4 * (c - b)^1 + (12 : ℝ) * (b - a)^3 * (c - b)^2 + (6 : ℝ) * (b - a)^2 * (c - b)^3 + (1 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*c - 3*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 + a*b^4 - 3*a*b^3*c - 3*a*b*c^3 + 2*b^2*c^3 + b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * a^3 * (c - a)^2 + (5 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (5 : ℝ) * a^3 * (b - c)^2 + (12 : ℝ) * a^2 * (c - a)^3 + (12 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (6 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^2 * (b - c)^3 + (10 : ℝ) * a^1 * (c - a)^4 + (12 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (3 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (1 : ℝ) * a^1 * (b - c)^4 + (3 : ℝ) * (c - a)^5 + (5 : ℝ) * (c - a)^4 * (b - c)^1 + (2 : ℝ) * (c - a)^3 * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*c - 3*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 + a*b^4 - 3*a*b^3*c - 3*a*b*c^3 + 2*b^2*c^3 + b*c^4) := by
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
  have hn : 0 ≤ (a^4*c - 3*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 + a*b^4 - 3*a*b^3*c - 3*a*b*c^3 + 2*b^2*c^3 + b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^2 * (a + 2 * c) / (3 * b) + b^2 * (b + 2 * a) / (3 * c) + c^2 * (c + 2 * b) / (3 * a) ≥ a^2 + b^2 + c^2) := @solution
#print axioms solution
