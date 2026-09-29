-- Prove2me | solution 1 for WorkbookSource.plus_22367
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:17.95102+00:00
-- url     : https://prove2.me/submissions/75a25234-249d-4f98-8d02-ec61d03177f6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 4 * (a / b + b / c + c / a) + (9 * a * b * c) / (a ^ 3 + b ^ 3 + c ^ 3 + 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2)) ≥ 13   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*c + 4*a^4*b^2 - 13*a^4*b*c + 8*a^4*c^2 + 16*a^3*b^2*c - 22*a^3*b*c^2 + 8*a^2*b^4 - 22*a^2*b^3*c + 9*a^2*b^2*c^2 + 16*a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^5 - 13*a*b^4*c + 16*a*b^3*c^2 - 22*a*b^2*c^3 - 13*a*b*c^4 + 4*b^4*c^2 + 8*b^2*c^4 + 4*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (31 : ℝ) * a^4 * (b - a)^2 + (31 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (31 : ℝ) * a^4 * (c - b)^2 + (94 : ℝ) * a^3 * (b - a)^3 + (158 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (124 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (30 : ℝ) * a^3 * (c - b)^3 + (115 : ℝ) * a^2 * (b - a)^4 + (264 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (249 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (100 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (19 : ℝ) * a^2 * (c - b)^4 + (68 : ℝ) * a^1 * (b - a)^5 + (201 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (240 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (142 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (43 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^6 + (60 : ℝ) * (b - a)^5 * (c - b)^1 + (92 : ℝ) * (b - a)^4 * (c - b)^2 + (72 : ℝ) * (b - a)^3 * (c - b)^3 + (28 : ℝ) * (b - a)^2 * (c - b)^4 + (4 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^5*c + 4*a^4*b^2 - 13*a^4*b*c + 8*a^4*c^2 + 16*a^3*b^2*c - 22*a^3*b*c^2 + 8*a^2*b^4 - 22*a^2*b^3*c + 9*a^2*b^2*c^2 + 16*a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^5 - 13*a*b^4*c + 16*a*b^3*c^2 - 22*a*b^2*c^3 - 13*a*b*c^4 + 4*b^4*c^2 + 8*b^2*c^4 + 4*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (31 : ℝ) * a^4 * (c - a)^2 + (31 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (31 : ℝ) * a^4 * (b - c)^2 + (94 : ℝ) * a^3 * (c - a)^3 + (124 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (90 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (30 : ℝ) * a^3 * (b - c)^3 + (115 : ℝ) * a^2 * (c - a)^4 + (196 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (147 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (66 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (19 : ℝ) * a^2 * (b - c)^4 + (68 : ℝ) * a^1 * (c - a)^5 + (139 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (116 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (52 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (15 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * a^1 * (b - c)^5 + (16 : ℝ) * (c - a)^6 + (36 : ℝ) * (c - a)^5 * (b - c)^1 + (32 : ℝ) * (c - a)^4 * (b - c)^2 + (16 : ℝ) * (c - a)^3 * (b - c)^3 + (4 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*c + 4*a^4*b^2 - 13*a^4*b*c + 8*a^4*c^2 + 16*a^3*b^2*c - 22*a^3*b*c^2 + 8*a^2*b^4 - 22*a^2*b^3*c + 9*a^2*b^2*c^2 + 16*a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^5 - 13*a*b^4*c + 16*a*b^3*c^2 - 22*a*b^2*c^3 - 13*a*b*c^4 + 4*b^4*c^2 + 8*b^2*c^4 + 4*b*c^5) := by
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
  have hn : 0 ≤ (4*a^5*c + 4*a^4*b^2 - 13*a^4*b*c + 8*a^4*c^2 + 16*a^3*b^2*c - 22*a^3*b*c^2 + 8*a^2*b^4 - 22*a^2*b^3*c + 9*a^2*b^2*c^2 + 16*a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^5 - 13*a*b^4*c + 16*a*b^3*c^2 - 22*a*b^2*c^3 - 13*a*b*c^4 + 4*b^4*c^2 + 8*b^2*c^4 + 4*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 4 * (a / b + b / c + c / a) + (9 * a * b * c) / (a ^ 3 + b ^ 3 + c ^ 3 + 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2)) ≥ 13) := @solution
#print axioms solution
