-- Prove2me | solution 1 for WorkbookSource.base_1827
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:57:07.797486+00:00
-- url     : https://prove2.me/submissions/c5011052-252b-4c80-be0a-79d9bb922f29

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (a + c) / b + (a + b) / c ≥ 4 * (a / (a + b) + b / (b + c) + c / (c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 + 2*a^4*b*c + a^4*c^2 + 2*a^3*b^3 - 4*a^3*b^2*c + 2*a^3*c^3 + a^2*b^4 - 6*a^2*b^2*c^2 - 4*a^2*b*c^3 + a^2*c^4 + 2*a*b^4*c - 4*a*b^3*c^2 + 2*a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (b - a)^2 + (16 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^4 * (c - b)^2 + (48 : ℝ) * a^3 * (b - a)^3 + (74 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (58 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16 : ℝ) * a^3 * (c - b)^3 + (52 : ℝ) * a^2 * (b - a)^4 + (108 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (90 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (34 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4 : ℝ) * a^2 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^5 + (62 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (60 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (26 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (13 : ℝ) * (b - a)^4 * (c - b)^2 + (6 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b^2 + 2*a^4*b*c + a^4*c^2 + 2*a^3*b^3 - 4*a^3*b^2*c + 2*a^3*c^3 + a^2*b^4 - 6*a^2*b^2*c^2 - 4*a^2*b*c^3 + a^2*c^4 + 2*a*b^4*c - 4*a*b^3*c^2 + 2*a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^4 * (c - a)^2 + (16 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (16 : ℝ) * a^4 * (b - c)^2 + (48 : ℝ) * a^3 * (c - a)^3 + (70 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (54 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (16 : ℝ) * a^3 * (b - c)^3 + (52 : ℝ) * a^2 * (c - a)^4 + (100 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (78 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (30 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (4 : ℝ) * a^2 * (b - c)^4 + (24 : ℝ) * a^1 * (c - a)^5 + (58 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (52 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (22 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (4 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * (c - a)^6 + (12 : ℝ) * (c - a)^5 * (b - c)^1 + (13 : ℝ) * (c - a)^4 * (b - c)^2 + (6 : ℝ) * (c - a)^3 * (b - c)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 + 2*a^4*b*c + a^4*c^2 + 2*a^3*b^3 - 4*a^3*b^2*c + 2*a^3*c^3 + a^2*b^4 - 6*a^2*b^2*c^2 - 4*a^2*b*c^3 + a^2*c^4 + 2*a*b^4*c - 4*a*b^3*c^2 + 2*a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by
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
  have hn : 0 ≤ (a^4*b^2 + 2*a^4*b*c + a^4*c^2 + 2*a^3*b^3 - 4*a^3*b^2*c + 2*a^3*c^3 + a^2*b^4 - 6*a^2*b^2*c^2 - 4*a^2*b*c^3 + a^2*c^4 + 2*a*b^4*c - 4*a*b^3*c^2 + 2*a*b*c^4 + b^4*c^2 + 2*b^3*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b + c) / a + (a + c) / b + (a + b) / c ≥ 4 * (a / (a + b) + b / (b + c) + c / (c + a))) := @solution
#print axioms solution
