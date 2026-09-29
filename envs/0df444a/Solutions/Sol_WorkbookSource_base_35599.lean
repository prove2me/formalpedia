-- Prove2me | solution 1 for WorkbookSource.base_35599
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:06:06.112647+00:00
-- url     : https://prove2.me/submissions/a68fcc27-bccd-4db8-8b13-863b4f247690

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 2 / b + 2 / c ≥ 2 * (1 / (a + b) + 3 / (b + c) + 1 / (c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^3*b^2 - 2*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a^2*b^2*c - 3*a^2*b*c^2 + 2*a^2*c^3 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + b^3*c^2 + b^2*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^3 * (b - a)^2 + (4 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^3 * (c - b)^2 + (10 : ℝ) * a^2 * (b - a)^3 + (15 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (13 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^2 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^4 + (16 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (11 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * (b - a)^5 + (5 : ℝ) * (b - a)^4 * (c - b)^1 + (4 : ℝ) * (b - a)^3 * (c - b)^2 + (1 : ℝ) * (b - a)^2 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ a) (hord2 : a ≤ c) : 0 ≤ (2*a^3*b^2 - 2*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a^2*b^2*c - 3*a^2*b*c^2 + 2*a^2*c^3 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + b^3*c^2 + b^2*c^3) := by
    have hdiff1 : 0 ≤ (a - b) := by linarith
    have hdiff2 : 0 ≤ (c - a) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * b^3 * (a - b)^2 + (12 : ℝ) * b^3 * (a - b)^1 * (c - a)^1 + (8 : ℝ) * b^3 * (c - a)^2 + (20 : ℝ) * b^2 * (a - b)^3 + (37 : ℝ) * b^2 * (a - b)^2 * (c - a)^1 + (23 : ℝ) * b^2 * (a - b)^1 * (c - a)^2 + (4 : ℝ) * b^2 * (c - a)^3 + (16 : ℝ) * b^1 * (a - b)^4 + (35 : ℝ) * b^1 * (a - b)^3 * (c - a)^1 + (24 : ℝ) * b^1 * (a - b)^2 * (c - a)^2 + (5 : ℝ) * b^1 * (a - b)^1 * (c - a)^3 + (4 : ℝ) * (a - b)^5 + (10 : ℝ) * (a - b)^4 * (c - a)^1 + (8 : ℝ) * (a - b)^3 * (c - a)^2 + (2 : ℝ) * (a - b)^2 * (c - a)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux2 (a b c : ℝ) (hlow : 0 ≤ b) (hord1 : b ≤ c) (hord2 : c ≤ a) : 0 ≤ (2*a^3*b^2 - 2*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a^2*b^2*c - 3*a^2*b*c^2 + 2*a^2*c^3 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + b^3*c^2 + b^2*c^3) := by
    have hdiff1 : 0 ≤ (c - b) := by linarith
    have hdiff2 : 0 ≤ (a - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * b^3 * (c - b)^2 + (4 : ℝ) * b^3 * (c - b)^1 * (a - c)^1 + (4 : ℝ) * b^3 * (a - c)^2 + (20 : ℝ) * b^2 * (c - b)^3 + (23 : ℝ) * b^2 * (c - b)^2 * (a - c)^1 + (9 : ℝ) * b^2 * (c - b)^1 * (a - c)^2 + (2 : ℝ) * b^2 * (a - c)^3 + (16 : ℝ) * b^1 * (c - b)^4 + (29 : ℝ) * b^1 * (c - b)^3 * (a - c)^1 + (15 : ℝ) * b^1 * (c - b)^2 * (a - c)^2 + (2 : ℝ) * b^1 * (c - b)^1 * (a - c)^3 + (4 : ℝ) * (c - b)^5 + (10 : ℝ) * (c - b)^4 * (a - c)^1 + (8 : ℝ) * (c - b)^3 * (a - c)^2 + (2 : ℝ) * (c - b)^2 * (a - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^3*b^2 - 2*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a^2*b^2*c - 3*a^2*b*c^2 + 2*a^2*c^3 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + b^3*c^2 + b^2*c^3) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux2 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux2 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (2*a^3*b^2 - 2*a^3*b*c + 2*a^3*c^2 + 2*a^2*b^3 - 3*a^2*b^2*c - 3*a^2*b*c^2 + 2*a^2*c^3 + a*b^3*c - 4*a*b^2*c^2 + a*b*c^3 + b^3*c^2 + b^2*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / a + 2 / b + 2 / c ≥ 2 * (1 / (a + b) + 3 / (b + c) + 1 / (c + a))) := @solution
#print axioms solution
