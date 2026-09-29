-- Prove2me | solution 1 for WorkbookSource.base_15933
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:04.455817+00:00
-- url     : https://prove2.me/submissions/8a575829-8d0b-457c-812c-2975680d0bac

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) / (2 * a + b) + (b + 2 * c) / (2 * b + c) + (c + 2 * a) / (2 * c + a) ≤ (9 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a + b + c) ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (24*a^4*b + 9*a^4*c - 15*a^3*b^2 + 21*a^3*b*c + 6*a^3*c^2 + 6*a^2*b^3 - 45*a^2*b^2*c - 45*a^2*b*c^2 - 15*a^2*c^3 + 9*a*b^4 + 21*a*b^3*c - 45*a*b^2*c^2 + 21*a*b*c^3 + 24*a*c^4 + 24*b^4*c - 15*b^3*c^2 + 6*b^2*c^3 + 9*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (135 : ℝ) * a^3 * (b - a)^2 + (135 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (135 : ℝ) * a^3 * (c - b)^2 + (261 : ℝ) * a^2 * (b - a)^3 + (378 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (405 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (144 : ℝ) * a^2 * (c - b)^3 + (150 : ℝ) * a^1 * (b - a)^4 + (282 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (333 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (201 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (33 : ℝ) * a^1 * (c - b)^4 + (24 : ℝ) * (b - a)^5 + (48 : ℝ) * (b - a)^4 * (c - b)^1 + (57 : ℝ) * (b - a)^3 * (c - b)^2 + (42 : ℝ) * (b - a)^2 * (c - b)^3 + (9 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (24*a^4*b + 9*a^4*c - 15*a^3*b^2 + 21*a^3*b*c + 6*a^3*c^2 + 6*a^2*b^3 - 45*a^2*b^2*c - 45*a^2*b*c^2 - 15*a^2*c^3 + 9*a*b^4 + 21*a*b^3*c - 45*a*b^2*c^2 + 21*a*b*c^3 + 24*a*c^4 + 24*b^4*c - 15*b^3*c^2 + 6*b^2*c^3 + 9*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (135 : ℝ) * a^3 * (c - a)^2 + (135 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (135 : ℝ) * a^3 * (b - c)^2 + (261 : ℝ) * a^2 * (c - a)^3 + (405 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (432 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (144 : ℝ) * a^2 * (b - c)^3 + (150 : ℝ) * a^1 * (c - a)^4 + (318 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (387 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (219 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (33 : ℝ) * a^1 * (b - c)^4 + (24 : ℝ) * (c - a)^5 + (72 : ℝ) * (c - a)^4 * (b - c)^1 + (105 : ℝ) * (c - a)^3 * (b - c)^2 + (81 : ℝ) * (c - a)^2 * (b - c)^3 + (24 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (24*a^4*b + 9*a^4*c - 15*a^3*b^2 + 21*a^3*b*c + 6*a^3*c^2 + 6*a^2*b^3 - 45*a^2*b^2*c - 45*a^2*b*c^2 - 15*a^2*c^3 + 9*a*b^4 + 21*a*b^3*c - 45*a*b^2*c^2 + 21*a*b*c^3 + 24*a*c^4 + 24*b^4*c - 15*b^3*c^2 + 6*b^2*c^3 + 9*b*c^4) := by
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
  have hn : 0 ≤ (24*a^4*b + 9*a^4*c - 15*a^3*b^2 + 21*a^3*b*c + 6*a^3*c^2 + 6*a^2*b^3 - 45*a^2*b^2*c - 45*a^2*b*c^2 - 15*a^2*c^3 + 9*a*b^4 + 21*a*b^3*c - 45*a*b^2*c^2 + 21*a*b*c^3 + 24*a*c^4 + 24*b^4*c - 15*b^3*c^2 + 6*b^2*c^3 + 9*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + 2 * b) / (2 * a + b) + (b + 2 * c) / (2 * b + c) + (c + 2 * a) / (2 * c + a) ≤ (9 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a + b + c) ^ 2) := @solution
#print axioms solution
