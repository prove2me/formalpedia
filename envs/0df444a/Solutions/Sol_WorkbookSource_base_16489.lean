-- Prove2me | solution 1 for WorkbookSource.base_16489
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:03:48.991281+00:00
-- url     : https://prove2.me/submissions/0580b5f2-10fe-416a-bacb-9df7f0eb6945

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * (a + b - 2 * c) / (b * c + 1) + b * (b + c - 2 * a) / (c * a + 1) + c * (c + a - 2 * b) / (a * b + 1)) ≥ 0  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b*c + a^3*b^2*c - 2*a^3*b*c^2 + a^3*b + a^3*c - 2*a^2*b^3*c - a^2*b^2 + a^2*b*c^3 - a^2*b*c - a^2*c^2 + a^2 + a*b^4*c + a*b^3*c^2 + a*b^3 - 2*a*b^2*c^3 - a*b^2*c + a*b*c^4 - a*b*c^2 - a*b + a*c^3 - a*c + b^3*c - b^2*c^2 + b^2 + b*c^3 - b*c + c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^4 * (b - a)^2 + (2 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^4 * (c - b)^2 + (5 : ℝ) * a^3 * (b - a)^3 + (6 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (7 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (3 : ℝ) * a^3 * (c - b)^3 + (4 : ℝ) * a^2 * (b - a)^4 + (5 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (6 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (3 : ℝ) * a^2 * (b - a)^2 + (5 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (3 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (1 : ℝ) * a^2 * (c - b)^4 + (3 : ℝ) * a^2 * (c - b)^2 + (1 : ℝ) * a^1 * (b - a)^5 + (1 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^3 + (2 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (6 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (2 : ℝ) * a^1 * (c - b)^3 + (1 : ℝ) * (b - a)^4 + (2 : ℝ) * (b - a)^3 * (c - b)^1 + (2 : ℝ) * (b - a)^2 * (c - b)^2 + (1 : ℝ) * (b - a)^2 + (1 : ℝ) * (b - a)^1 * (c - b)^3 + (1 : ℝ) * (b - a)^1 * (c - b)^1 + (1 : ℝ) * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b*c + a^3*b^2*c - 2*a^3*b*c^2 + a^3*b + a^3*c - 2*a^2*b^3*c - a^2*b^2 + a^2*b*c^3 - a^2*b*c - a^2*c^2 + a^2 + a*b^4*c + a*b^3*c^2 + a*b^3 - 2*a*b^2*c^3 - a*b^2*c + a*b*c^4 - a*b*c^2 - a*b + a*c^3 - a*c + b^3*c - b^2*c^2 + b^2 + b*c^3 - b*c + c^2) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^4 * (c - a)^2 + (2 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (2 : ℝ) * a^4 * (b - c)^2 + (5 : ℝ) * a^3 * (c - a)^3 + (9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (10 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (3 : ℝ) * a^3 * (b - c)^3 + (4 : ℝ) * a^2 * (c - a)^4 + (11 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (15 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (3 : ℝ) * a^2 * (c - a)^2 + (8 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (3 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (1 : ℝ) * a^2 * (b - c)^4 + (3 : ℝ) * a^2 * (b - c)^2 + (1 : ℝ) * a^1 * (c - a)^5 + (4 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (7 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (4 : ℝ) * a^1 * (c - a)^3 + (5 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (6 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (6 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (2 : ℝ) * a^1 * (b - c)^3 + (1 : ℝ) * (c - a)^4 + (2 : ℝ) * (c - a)^3 * (b - c)^1 + (2 : ℝ) * (c - a)^2 * (b - c)^2 + (1 : ℝ) * (c - a)^2 + (1 : ℝ) * (c - a)^1 * (b - c)^3 + (1 : ℝ) * (c - a)^1 * (b - c)^1 + (1 : ℝ) * (b - c)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b*c + a^3*b^2*c - 2*a^3*b*c^2 + a^3*b + a^3*c - 2*a^2*b^3*c - a^2*b^2 + a^2*b*c^3 - a^2*b*c - a^2*c^2 + a^2 + a*b^4*c + a*b^3*c^2 + a*b^3 - 2*a*b^2*c^3 - a*b^2*c + a*b*c^4 - a*b*c^2 - a*b + a*c^3 - a*c + b^3*c - b^2*c^2 + b^2 + b*c^3 - b*c + c^2) := by
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
  have hn : 0 ≤ (a^4*b*c + a^3*b^2*c - 2*a^3*b*c^2 + a^3*b + a^3*c - 2*a^2*b^3*c - a^2*b^2 + a^2*b*c^3 - a^2*b*c - a^2*c^2 + a^2 + a*b^4*c + a*b^3*c^2 + a*b^3 - 2*a*b^2*c^3 - a*b^2*c + a*b*c^4 - a*b*c^2 - a*b + a*c^3 - a*c + b^3*c - b^2*c^2 + b^2 + b*c^3 - b*c + c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a * (a + b - 2 * c) / (b * c + 1) + b * (b + c - 2 * a) / (c * a + 1) + c * (c + a - 2 * b) / (a * b + 1)) ≥ 0) := @solution
#print axioms solution
