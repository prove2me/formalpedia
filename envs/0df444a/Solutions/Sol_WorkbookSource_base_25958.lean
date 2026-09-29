-- Prove2me | solution 1 for WorkbookSource.base_25958
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:06:30.548965+00:00
-- url     : https://prove2.me/submissions/12f7280f-9f76-4d4f-8fb2-a43523165d44

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ (a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b)) + 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + 4*a^2*b^4 - 18*a^2*b^2*c^2 + 2*b^3*c^3 + 4*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (22 : ℝ) * a^4 * (b - a)^2 + (22 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (22 : ℝ) * a^4 * (c - b)^2 + (68 : ℝ) * a^3 * (b - a)^3 + (118 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (90 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (20 : ℝ) * a^3 * (c - b)^3 + (76 : ℝ) * a^2 * (b - a)^4 + (184 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (162 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (54 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (36 : ℝ) * a^1 * (b - a)^5 + (110 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (120 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (54 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * (b - a)^6 + (22 : ℝ) * (b - a)^5 * (c - b)^1 + (30 : ℝ) * (b - a)^4 * (c - b)^2 + (18 : ℝ) * (b - a)^3 * (c - b)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + 4*a^2*b^4 - 18*a^2*b^2*c^2 + 2*b^3*c^3 + 4*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (22 : ℝ) * a^4 * (c - a)^2 + (22 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (22 : ℝ) * a^4 * (b - c)^2 + (68 : ℝ) * a^3 * (c - a)^3 + (86 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (58 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (20 : ℝ) * a^3 * (b - c)^3 + (76 : ℝ) * a^2 * (c - a)^4 + (120 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (66 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (22 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (36 : ℝ) * a^1 * (c - a)^5 + (70 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (40 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (6 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (6 : ℝ) * (c - a)^6 + (14 : ℝ) * (c - a)^5 * (b - c)^1 + (10 : ℝ) * (c - a)^4 * (b - c)^2 + (2 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + 4*a^2*b^4 - 18*a^2*b^2*c^2 + 2*b^3*c^3 + 4*b^2*c^4) := by
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
  have hn : 0 ≤ (4*a^4*c^2 + 2*a^3*b^3 + 2*a^3*c^3 + 4*a^2*b^4 - 18*a^2*b^2*c^2 + 2*b^3*c^3 + 4*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a) ≥ (a / (b + 2 * c) + b / (c + 2 * a) + c / (a + 2 * b)) + 2) := @solution
#print axioms solution
