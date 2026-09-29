-- Prove2me | solution 1 for WorkbookSource.base_47864
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:21:24.595015+00:00
-- url     : https://prove2.me/submissions/920569b4-159e-4ad5-8935-163b83c870ef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * (a + b)^3 + b^2 * (b + c)^3 + c^2 * (c + a)^3 ≥ (8 * a * b * c * (a + b + c)^2) / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^5 + 9*a^4*b + 9*a^3*b^2 - 8*a^3*b*c + 3*a^3*c^2 + 3*a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 9*a^2*c^3 - 8*a*b^3*c - 16*a*b^2*c^2 - 8*a*b*c^3 + 9*a*c^4 + 3*b^5 + 9*b^4*c + 9*b^3*c^2 + 3*b^2*c^3 + 3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (76 : ℝ) * a^3 * (b - a)^2 + (76 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (76 : ℝ) * a^3 * (c - b)^2 + (158 : ℝ) * a^2 * (b - a)^3 + (201 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (183 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (70 : ℝ) * a^2 * (c - b)^3 + (112 : ℝ) * a^1 * (b - a)^4 + (176 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (158 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (94 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (24 : ℝ) * a^1 * (c - b)^4 + (27 : ℝ) * (b - a)^5 + (51 : ℝ) * (b - a)^4 * (c - b)^1 + (48 : ℝ) * (b - a)^3 * (c - b)^2 + (33 : ℝ) * (b - a)^2 * (c - b)^3 + (15 : ℝ) * (b - a)^1 * (c - b)^4 + (3 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^5 + 9*a^4*b + 9*a^3*b^2 - 8*a^3*b*c + 3*a^3*c^2 + 3*a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 9*a^2*c^3 - 8*a*b^3*c - 16*a*b^2*c^2 - 8*a*b*c^3 + 9*a*c^4 + 3*b^5 + 9*b^4*c + 9*b^3*c^2 + 3*b^2*c^3 + 3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (76 : ℝ) * a^3 * (c - a)^2 + (76 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (76 : ℝ) * a^3 * (b - c)^2 + (158 : ℝ) * a^2 * (c - a)^3 + (273 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (255 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (70 : ℝ) * a^2 * (b - c)^3 + (112 : ℝ) * a^1 * (c - a)^4 + (272 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (302 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (142 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (24 : ℝ) * a^1 * (b - c)^4 + (27 : ℝ) * (c - a)^5 + (84 : ℝ) * (c - a)^4 * (b - c)^1 + (114 : ℝ) * (c - a)^3 * (b - c)^2 + (75 : ℝ) * (c - a)^2 * (b - c)^3 + (24 : ℝ) * (c - a)^1 * (b - c)^4 + (3 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^5 + 9*a^4*b + 9*a^3*b^2 - 8*a^3*b*c + 3*a^3*c^2 + 3*a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 9*a^2*c^3 - 8*a*b^3*c - 16*a*b^2*c^2 - 8*a*b*c^3 + 9*a*c^4 + 3*b^5 + 9*b^4*c + 9*b^3*c^2 + 3*b^2*c^3 + 3*c^5) := by
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
  have hn : 0 ≤ (3*a^5 + 9*a^4*b + 9*a^3*b^2 - 8*a^3*b*c + 3*a^3*c^2 + 3*a^2*b^3 - 16*a^2*b^2*c - 16*a^2*b*c^2 + 9*a^2*c^3 - 8*a*b^3*c - 16*a*b^2*c^2 - 8*a*b*c^3 + 9*a*c^4 + 3*b^5 + 9*b^4*c + 9*b^3*c^2 + 3*b^2*c^3 + 3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^2 * (a + b)^3 + b^2 * (b + c)^3 + c^2 * (c + a)^3 ≥ (8 * a * b * c * (a + b + c)^2) / 3) := @solution
#print axioms solution
