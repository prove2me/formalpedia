-- Prove2me | solution 1 for WorkbookSource.plus_75470
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:28.982155+00:00
-- url     : https://prove2.me/submissions/0941a030-554d-4baf-a7a3-676d69865f21

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 6 + 2 * c / a + 2 * a / b + 2 * b / c ≤ 3 * b * c / a ^ 2 + c / b + 3 * a * c / b ^ 2 + a / c + 3 * a * b / c ^ 2 + b / a   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^3*b^3 + a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 + a^2*b*c^3 + a*b^3*c^2 - 2*a*b^2*c^3 + 3*b^3*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (27 : ℝ) * a^3 * (b - a)^3 + (39 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (22 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (5 : ℝ) * a^3 * (c - b)^3 + (33 : ℝ) * a^2 * (b - a)^4 + (63 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (36 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (6 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (17 : ℝ) * a^1 * (b - a)^5 + (41 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (31 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (7 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (3 : ℝ) * (b - a)^6 + (9 : ℝ) * (b - a)^5 * (c - b)^1 + (9 : ℝ) * (b - a)^4 * (c - b)^2 + (3 : ℝ) * (b - a)^3 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^3*b^3 + a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 + a^2*b*c^3 + a*b^3*c^2 - 2*a*b^2*c^3 + 3*b^3*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (c - a)^2 + (8 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (8 : ℝ) * a^4 * (b - c)^2 + (27 : ℝ) * a^3 * (c - a)^3 + (42 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (25 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (5 : ℝ) * a^3 * (b - c)^3 + (33 : ℝ) * a^2 * (c - a)^4 + (69 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (45 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (17 : ℝ) * a^1 * (c - a)^5 + (44 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (37 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (10 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (3 : ℝ) * (c - a)^6 + (9 : ℝ) * (c - a)^5 * (b - c)^1 + (9 : ℝ) * (c - a)^4 * (b - c)^2 + (3 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^3*b^3 + a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 + a^2*b*c^3 + a*b^3*c^2 - 2*a*b^2*c^3 + 3*b^3*c^3) := by
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
  have hn : 0 ≤ (3*a^3*b^3 + a^3*b^2*c - 2*a^3*b*c^2 + 3*a^3*c^3 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 + a^2*b*c^3 + a*b^3*c^2 - 2*a*b^2*c^3 + 3*b^3*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 6 + 2 * c / a + 2 * a / b + 2 * b / c ≤ 3 * b * c / a ^ 2 + c / b + 3 * a * c / b ^ 2 + a / c + 3 * a * b / c ^ 2 + b / a) := @solution
#print axioms solution
