-- Prove2me | solution 1 for WorkbookSource.base_18837
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:37:19.976991+00:00
-- url     : https://prove2.me/submissions/78408241-aa82-4b89-be43-98ac1b3d8245

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b)) ≥ (a^2 + b^2 + c^2) / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^5 + 10*a^4*b - a^4*c - 4*a^3*b^2 - 3*a^3*b*c - 2*a^3*c^2 - 2*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - 4*a^2*c^3 - a*b^4 - 3*a*b^3*c - 6*a*b^2*c^2 - 3*a*b*c^3 + 10*a*c^4 + 6*b^5 + 10*b^4*c - 4*b^3*c^2 - 2*b^2*c^3 - b*c^4 + 6*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (69 : ℝ) * a^3 * (b - a)^2 + (69 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (69 : ℝ) * a^3 * (c - b)^2 + (120 : ℝ) * a^2 * (b - a)^3 + (150 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (204 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (87 : ℝ) * a^2 * (c - b)^3 + (72 : ℝ) * a^1 * (b - a)^4 + (104 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (177 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (145 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (39 : ℝ) * a^1 * (c - b)^4 + (15 : ℝ) * (b - a)^5 + (22 : ℝ) * (b - a)^4 * (c - b)^1 + (44 : ℝ) * (b - a)^3 * (c - b)^2 + (54 : ℝ) * (b - a)^2 * (c - b)^3 + (29 : ℝ) * (b - a)^1 * (c - b)^4 + (6 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (6*a^5 + 10*a^4*b - a^4*c - 4*a^3*b^2 - 3*a^3*b*c - 2*a^3*c^2 - 2*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - 4*a^2*c^3 - a*b^4 - 3*a*b^3*c - 6*a*b^2*c^2 - 3*a*b*c^3 + 10*a*c^4 + 6*b^5 + 10*b^4*c - 4*b^3*c^2 - 2*b^2*c^3 - b*c^4 + 6*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (69 : ℝ) * a^3 * (c - a)^2 + (69 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (69 : ℝ) * a^3 * (b - c)^2 + (120 : ℝ) * a^2 * (c - a)^3 + (210 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (264 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (87 : ℝ) * a^2 * (b - c)^3 + (72 : ℝ) * a^1 * (c - a)^4 + (184 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (297 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (185 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (39 : ℝ) * a^1 * (b - c)^4 + (15 : ℝ) * (c - a)^5 + (53 : ℝ) * (c - a)^4 * (b - c)^1 + (106 : ℝ) * (c - a)^3 * (b - c)^2 + (96 : ℝ) * (c - a)^2 * (b - c)^3 + (40 : ℝ) * (c - a)^1 * (b - c)^4 + (6 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^5 + 10*a^4*b - a^4*c - 4*a^3*b^2 - 3*a^3*b*c - 2*a^3*c^2 - 2*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - 4*a^2*c^3 - a*b^4 - 3*a*b^3*c - 6*a*b^2*c^2 - 3*a*b*c^3 + 10*a*c^4 + 6*b^5 + 10*b^4*c - 4*b^3*c^2 - 2*b^2*c^3 - b*c^4 + 6*c^5) := by
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
  have hn : 0 ≤ (6*a^5 + 10*a^4*b - a^4*c - 4*a^3*b^2 - 3*a^3*b*c - 2*a^3*c^2 - 2*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - 4*a^2*c^3 - a*b^4 - 3*a*b^3*c - 6*a*b^2*c^2 - 3*a*b*c^3 + 10*a*c^4 + 6*b^5 + 10*b^4*c - 4*b^3*c^2 - 2*b^2*c^3 - b*c^4 + 6*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b)) ≥ (a^2 + b^2 + c^2) / 3) := @solution
#print axioms solution
