-- Prove2me | solution 1 for WorkbookSource.base_21812
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:50:59.89272+00:00
-- url     : https://prove2.me/submissions/50648e9c-2163-4b60-aca2-0ece7fe4f519

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a)) ≥ (a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^4*b^2 + 6*a^4*b*c + 4*a^4*c^2 + 6*a^3*b^3 - 4*a^3*b^2*c + a^3*b*c^2 + 6*a^3*c^3 + 4*a^2*b^4 + a^2*b^3*c - 63*a^2*b^2*c^2 - 4*a^2*b*c^3 + 8*a^2*c^4 + 6*a*b^4*c - 4*a*b^3*c^2 + a*b^2*c^3 + 6*a*b*c^4 + 8*b^4*c^2 + 6*b^3*c^3 + 4*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (81 : ℝ) * a^4 * (b - a)^2 + (81 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (81 : ℝ) * a^4 * (c - b)^2 + (243 : ℝ) * a^3 * (b - a)^3 + (351 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (270 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (81 : ℝ) * a^3 * (c - b)^3 + (261 : ℝ) * a^2 * (b - a)^4 + (495 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (378 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (144 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (18 : ℝ) * a^2 * (c - b)^4 + (117 : ℝ) * a^1 * (b - a)^5 + (275 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (235 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (91 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (14 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * (b - a)^6 + (50 : ℝ) * (b - a)^5 * (c - b)^1 + (50 : ℝ) * (b - a)^4 * (c - b)^2 + (22 : ℝ) * (b - a)^3 * (c - b)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (8*a^4*b^2 + 6*a^4*b*c + 4*a^4*c^2 + 6*a^3*b^3 - 4*a^3*b^2*c + a^3*b*c^2 + 6*a^3*c^3 + 4*a^2*b^4 + a^2*b^3*c - 63*a^2*b^2*c^2 - 4*a^2*b*c^3 + 8*a^2*c^4 + 6*a*b^4*c - 4*a*b^3*c^2 + a*b^2*c^3 + 6*a*b*c^4 + 8*b^4*c^2 + 6*b^3*c^3 + 4*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (81 : ℝ) * a^4 * (c - a)^2 + (81 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (81 : ℝ) * a^4 * (b - c)^2 + (243 : ℝ) * a^3 * (c - a)^3 + (378 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (297 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (81 : ℝ) * a^3 * (b - c)^3 + (261 : ℝ) * a^2 * (c - a)^4 + (549 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (459 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (171 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (18 : ℝ) * a^2 * (b - c)^4 + (117 : ℝ) * a^1 * (c - a)^5 + (310 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (305 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (134 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (22 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (18 : ℝ) * (c - a)^6 + (58 : ℝ) * (c - a)^5 * (b - c)^1 + (70 : ℝ) * (c - a)^4 * (b - c)^2 + (38 : ℝ) * (c - a)^3 * (b - c)^3 + (8 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^4*b^2 + 6*a^4*b*c + 4*a^4*c^2 + 6*a^3*b^3 - 4*a^3*b^2*c + a^3*b*c^2 + 6*a^3*c^3 + 4*a^2*b^4 + a^2*b^3*c - 63*a^2*b^2*c^2 - 4*a^2*b*c^3 + 8*a^2*c^4 + 6*a*b^4*c - 4*a*b^3*c^2 + a*b^2*c^3 + 6*a*b*c^4 + 8*b^4*c^2 + 6*b^3*c^3 + 4*b^2*c^4) := by
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
  have hn : 0 ≤ (8*a^4*b^2 + 6*a^4*b*c + 4*a^4*c^2 + 6*a^3*b^3 - 4*a^3*b^2*c + a^3*b*c^2 + 6*a^3*c^3 + 4*a^2*b^4 + a^2*b^3*c - 63*a^2*b^2*c^2 - 4*a^2*b*c^3 + 8*a^2*c^4 + 6*a*b^4*c - 4*a*b^3*c^2 + a*b^2*c^3 + 6*a*b*c^4 + 8*b^4*c^2 + 6*b^3*c^3 + 4*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (a + 2 * b) + b / (b + 2 * c) + c / (c + 2 * a)) ≥ (a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a))) := @solution
#print axioms solution
