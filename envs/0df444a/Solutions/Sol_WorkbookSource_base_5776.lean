-- Prove2me | solution 1 for WorkbookSource.base_5776
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:42.500635+00:00
-- url     : https://prove2.me/submissions/dafc828d-adfa-4800-ae23-a234fc758126

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (c * c + a * b + b * c) + b * c / (a * a + b * c + c * a) + c * a / (b * b + c * a + a * b)) ≥ 3 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 + 5*a^4*b*c + a^3*b^3 - 2*a^3*b^2*c + 3*a^3*b*c^2 + a^3*c^3 + 3*a^2*b^3*c + 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*c^4 + 5*a*b^4*c - 2*a*b^3*c^2 + 3*a*b^2*c^3 + 5*a*b*c^4 + b^4*c^2 + b^3*c^3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^6 + (108 : ℝ) * a^5 * (b - a)^1 + (54 : ℝ) * a^5 * (c - b)^1 + (185 : ℝ) * a^4 * (b - a)^2 + (185 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (50 : ℝ) * a^4 * (c - b)^2 + (173 : ℝ) * a^3 * (b - a)^3 + (258 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (139 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (27 : ℝ) * a^3 * (c - b)^3 + (90 : ℝ) * a^2 * (b - a)^4 + (177 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (138 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (51 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^2 * (c - b)^4 + (23 : ℝ) * a^1 * (b - a)^5 + (55 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (53 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (26 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (5 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (b - a)^6 + (5 : ℝ) * (b - a)^5 * (c - b)^1 + (4 : ℝ) * (b - a)^4 * (c - b)^2 + (1 : ℝ) * (b - a)^3 * (c - b)^3 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^4*b^2 + 5*a^4*b*c + a^3*b^3 - 2*a^3*b^2*c + 3*a^3*b*c^2 + a^3*c^3 + 3*a^2*b^3*c + 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*c^4 + 5*a*b^4*c - 2*a*b^3*c^2 + 3*a*b^2*c^3 + 5*a*b*c^4 + b^4*c^2 + b^3*c^3) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^6 + (108 : ℝ) * a^5 * (c - a)^1 + (54 : ℝ) * a^5 * (b - c)^1 + (185 : ℝ) * a^4 * (c - a)^2 + (185 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (50 : ℝ) * a^4 * (b - c)^2 + (173 : ℝ) * a^3 * (c - a)^3 + (261 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (142 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (27 : ℝ) * a^3 * (b - c)^3 + (90 : ℝ) * a^2 * (c - a)^4 + (183 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (147 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (54 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (6 : ℝ) * a^2 * (b - c)^4 + (23 : ℝ) * a^1 * (c - a)^5 + (60 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (63 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (33 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (7 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * (c - a)^6 + (7 : ℝ) * (c - a)^5 * (b - c)^1 + (9 : ℝ) * (c - a)^4 * (b - c)^2 + (5 : ℝ) * (c - a)^3 * (b - c)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 + 5*a^4*b*c + a^3*b^3 - 2*a^3*b^2*c + 3*a^3*b*c^2 + a^3*c^3 + 3*a^2*b^3*c + 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*c^4 + 5*a*b^4*c - 2*a*b^3*c^2 + 3*a*b^2*c^3 + 5*a*b*c^4 + b^4*c^2 + b^3*c^3) := by
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
  have hn : 0 ≤ (a^4*b^2 + 5*a^4*b*c + a^3*b^3 - 2*a^3*b^2*c + 3*a^3*b*c^2 + a^3*c^3 + 3*a^2*b^3*c + 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*c^4 + 5*a*b^4*c - 2*a*b^3*c^2 + 3*a*b^2*c^3 + 5*a*b*c^4 + b^4*c^2 + b^3*c^3) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b / (c * c + a * b + b * c) + b * c / (a * a + b * c + c * a) + c * a / (b * b + c * a + a * b)) ≥ 3 / 4) := @solution
#print axioms solution
