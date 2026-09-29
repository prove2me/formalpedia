-- Prove2me | solution 1 for WorkbookSource.base_13043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:06.219038+00:00
-- url     : https://prove2.me/submissions/2e986b4c-5688-4ed1-84c6-49eee48c0a43

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 / 4 + a / (a + b) + b / (b + c) + c / (c + a)) ≥ (9 / 4) * (a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^4*b^2 + 5*a^4*b*c + 5*a^4*c^2 + 5*a^3*b^3 + a^3*b^2*c - 11*a^3*b*c^2 + 5*a^3*c^3 + 5*a^2*b^4 - 11*a^2*b^3*c - 39*a^2*b^2*c^2 + a^2*b*c^3 + 8*a^2*c^4 + 5*a*b^4*c + a*b^3*c^2 - 11*a*b^2*c^3 + 5*a*b*c^4 + 8*b^4*c^2 + 5*b^3*c^3 + 5*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^4 * (b - a)^2 + (72 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (72 : ℝ) * a^4 * (c - b)^2 + (216 : ℝ) * a^3 * (b - a)^3 + (306 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (234 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (72 : ℝ) * a^3 * (c - b)^3 + (234 : ℝ) * a^2 * (b - a)^4 + (432 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (324 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (126 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (18 : ℝ) * a^2 * (c - b)^4 + (108 : ℝ) * a^1 * (b - a)^5 + (249 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (210 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (84 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (15 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * (b - a)^6 + (51 : ℝ) * (b - a)^5 * (c - b)^1 + (53 : ℝ) * (b - a)^4 * (c - b)^2 + (25 : ℝ) * (b - a)^3 * (c - b)^3 + (5 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (8*a^4*b^2 + 5*a^4*b*c + 5*a^4*c^2 + 5*a^3*b^3 + a^3*b^2*c - 11*a^3*b*c^2 + 5*a^3*c^3 + 5*a^2*b^4 - 11*a^2*b^3*c - 39*a^2*b^2*c^2 + a^2*b*c^3 + 8*a^2*c^4 + 5*a*b^4*c + a*b^3*c^2 - 11*a*b^2*c^3 + 5*a*b*c^4 + 8*b^4*c^2 + 5*b^3*c^3 + 5*b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^4 * (c - a)^2 + (72 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (72 : ℝ) * a^4 * (b - c)^2 + (216 : ℝ) * a^3 * (c - a)^3 + (342 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (270 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (72 : ℝ) * a^3 * (b - c)^3 + (234 : ℝ) * a^2 * (c - a)^4 + (504 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (432 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (162 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (18 : ℝ) * a^2 * (b - c)^4 + (108 : ℝ) * a^1 * (c - a)^5 + (291 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (294 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (132 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (21 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (18 : ℝ) * (c - a)^6 + (57 : ℝ) * (c - a)^5 * (b - c)^1 + (68 : ℝ) * (c - a)^4 * (b - c)^2 + (37 : ℝ) * (c - a)^3 * (b - c)^3 + (8 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^4*b^2 + 5*a^4*b*c + 5*a^4*c^2 + 5*a^3*b^3 + a^3*b^2*c - 11*a^3*b*c^2 + 5*a^3*c^3 + 5*a^2*b^4 - 11*a^2*b^3*c - 39*a^2*b^2*c^2 + a^2*b*c^3 + 8*a^2*c^4 + 5*a*b^4*c + a*b^3*c^2 - 11*a*b^2*c^3 + 5*a*b*c^4 + 8*b^4*c^2 + 5*b^3*c^3 + 5*b^2*c^4) := by
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
  have hn : 0 ≤ (8*a^4*b^2 + 5*a^4*b*c + 5*a^4*c^2 + 5*a^3*b^3 + a^3*b^2*c - 11*a^3*b*c^2 + 5*a^3*c^3 + 5*a^2*b^4 - 11*a^2*b^3*c - 39*a^2*b^2*c^2 + a^2*b*c^3 + 8*a^2*c^4 + 5*a*b^4*c + a*b^3*c^2 - 11*a*b^2*c^3 + 5*a*b*c^4 + 8*b^4*c^2 + 5*b^3*c^3 + 5*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 / 4 + a / (a + b) + b / (b + c) + c / (c + a)) ≥ (9 / 4) * (a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a))) := @solution
#print axioms solution
