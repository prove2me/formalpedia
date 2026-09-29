-- Prove2me | solution 1 for WorkbookSource.base_40047
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:34.944676+00:00
-- url     : https://prove2.me/submissions/954cbd31-2347-4d27-af91-cb08cfa9b429

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / c) * (b / (c + a) + c / a) * (c / (a + b) + a / b) ≥ 27 / 8  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^4*b*c + 8*a^4*c^2 + 8*a^3*b^3 - 3*a^3*b^2*c - 11*a^3*b*c^2 + 8*a^3*c^3 + 8*a^2*b^4 - 11*a^2*b^3*c - 30*a^2*b^2*c^2 - 3*a^2*b*c^3 + 8*a*b^4*c - 3*a*b^3*c^2 - 11*a*b^2*c^3 + 8*a*b*c^4 + 8*b^3*c^3 + 8*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (66 : ℝ) * a^4 * (b - a)^2 + (66 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (66 : ℝ) * a^4 * (c - b)^2 + (198 : ℝ) * a^3 * (b - a)^3 + (325 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (259 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (66 : ℝ) * a^3 * (c - b)^3 + (214 : ℝ) * a^2 * (b - a)^4 + (484 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (429 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (159 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (16 : ℝ) * a^2 * (c - b)^4 + (98 : ℝ) * a^1 * (b - a)^5 + (281 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (300 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (141 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (24 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (16 : ℝ) * (b - a)^6 + (56 : ℝ) * (b - a)^5 * (c - b)^1 + (72 : ℝ) * (b - a)^4 * (c - b)^2 + (40 : ℝ) * (b - a)^3 * (c - b)^3 + (8 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (8*a^4*b*c + 8*a^4*c^2 + 8*a^3*b^3 - 3*a^3*b^2*c - 11*a^3*b*c^2 + 8*a^3*c^3 + 8*a^2*b^4 - 11*a^2*b^3*c - 30*a^2*b^2*c^2 - 3*a^2*b*c^3 + 8*a*b^4*c - 3*a*b^3*c^2 - 11*a*b^2*c^3 + 8*a*b*c^4 + 8*b^3*c^3 + 8*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (66 : ℝ) * a^4 * (c - a)^2 + (66 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (66 : ℝ) * a^4 * (b - c)^2 + (198 : ℝ) * a^3 * (c - a)^3 + (269 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (203 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (66 : ℝ) * a^3 * (b - c)^3 + (214 : ℝ) * a^2 * (c - a)^4 + (372 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (261 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (103 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (16 : ℝ) * a^2 * (b - c)^4 + (98 : ℝ) * a^1 * (c - a)^5 + (209 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (156 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (53 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (8 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (16 : ℝ) * (c - a)^6 + (40 : ℝ) * (c - a)^5 * (b - c)^1 + (32 : ℝ) * (c - a)^4 * (b - c)^2 + (8 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^4*b*c + 8*a^4*c^2 + 8*a^3*b^3 - 3*a^3*b^2*c - 11*a^3*b*c^2 + 8*a^3*c^3 + 8*a^2*b^4 - 11*a^2*b^3*c - 30*a^2*b^2*c^2 - 3*a^2*b*c^3 + 8*a*b^4*c - 3*a*b^3*c^2 - 11*a*b^2*c^3 + 8*a*b*c^4 + 8*b^3*c^3 + 8*b^2*c^4) := by
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
  have hn : 0 ≤ (8*a^4*b*c + 8*a^4*c^2 + 8*a^3*b^3 - 3*a^3*b^2*c - 11*a^3*b*c^2 + 8*a^3*c^3 + 8*a^2*b^4 - 11*a^2*b^3*c - 30*a^2*b^2*c^2 - 3*a^2*b*c^3 + 8*a*b^4*c - 3*a*b^3*c^2 - 11*a*b^2*c^3 + 8*a*b*c^4 + 8*b^3*c^3 + 8*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / c) * (b / (c + a) + c / a) * (c / (a + b) + a / b) ≥ 27 / 8) := @solution
#print axioms solution
