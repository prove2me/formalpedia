-- Prove2me | solution 1 for WorkbookSource.plus_55238
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:53.216137+00:00
-- url     : https://prove2.me/submissions/53c8909a-9fc7-465a-ae9d-aa76ff268bac

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 4 * ((3 * a + b) * a ^ 2 / (b + c) + (3 * b + c) * b ^ 2 / (c + a) + (3 * c + a) * c ^ 2 / (a + b)) ≥ 11 * (a ^ 2 + b ^ 2 + c ^ 2) - 3 * (a * b + b * c + c * a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (12*a^5 + 5*a^4*b + a^4*c - 4*a^3*b^2 - 8*a^3*c^2 - 8*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - 4*a^2*c^3 + a*b^4 - 6*a*b^2*c^2 + 5*a*c^4 + 12*b^5 + 5*b^4*c - 4*b^3*c^2 - 8*b^2*c^3 + b*c^4 + 12*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^3 * (b - a)^2 + (96 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^3 * (c - b)^2 + (156 : ℝ) * a^2 * (b - a)^3 + (216 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (324 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (132 : ℝ) * a^2 * (c - b)^3 + (90 : ℝ) * a^1 * (b - a)^4 + (156 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (318 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (252 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (66 : ℝ) * a^1 * (c - b)^4 + (18 : ℝ) * (b - a)^5 + (37 : ℝ) * (b - a)^4 * (c - b)^1 + (98 : ℝ) * (b - a)^3 * (c - b)^2 + (116 : ℝ) * (b - a)^2 * (c - b)^3 + (61 : ℝ) * (b - a)^1 * (c - b)^4 + (12 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (12*a^5 + 5*a^4*b + a^4*c - 4*a^3*b^2 - 8*a^3*c^2 - 8*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - 4*a^2*c^3 + a*b^4 - 6*a*b^2*c^2 + 5*a*c^4 + 12*b^5 + 5*b^4*c - 4*b^3*c^2 - 8*b^2*c^3 + b*c^4 + 12*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^3 * (c - a)^2 + (96 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (96 : ℝ) * a^3 * (b - c)^2 + (156 : ℝ) * a^2 * (c - a)^3 + (252 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (360 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (132 : ℝ) * a^2 * (b - c)^3 + (90 : ℝ) * a^1 * (c - a)^4 + (204 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (390 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (276 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (66 : ℝ) * a^1 * (b - c)^4 + (18 : ℝ) * (c - a)^5 + (53 : ℝ) * (c - a)^4 * (b - c)^1 + (130 : ℝ) * (c - a)^3 * (b - c)^2 + (136 : ℝ) * (c - a)^2 * (b - c)^3 + (65 : ℝ) * (c - a)^1 * (b - c)^4 + (12 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*a^5 + 5*a^4*b + a^4*c - 4*a^3*b^2 - 8*a^3*c^2 - 8*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - 4*a^2*c^3 + a*b^4 - 6*a*b^2*c^2 + 5*a*c^4 + 12*b^5 + 5*b^4*c - 4*b^3*c^2 - 8*b^2*c^3 + b*c^4 + 12*c^5) := by
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
  have hn : 0 ≤ (12*a^5 + 5*a^4*b + a^4*c - 4*a^3*b^2 - 8*a^3*c^2 - 8*a^2*b^3 - 6*a^2*b^2*c - 6*a^2*b*c^2 - 4*a^2*c^3 + a*b^4 - 6*a*b^2*c^2 + 5*a*c^4 + 12*b^5 + 5*b^4*c - 4*b^3*c^2 - 8*b^2*c^3 + b*c^4 + 12*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 4 * ((3 * a + b) * a ^ 2 / (b + c) + (3 * b + c) * b ^ 2 / (c + a) + (3 * c + a) * c ^ 2 / (a + b)) ≥ 11 * (a ^ 2 + b ^ 2 + c ^ 2) - 3 * (a * b + b * c + c * a)) := @solution
#print axioms solution
