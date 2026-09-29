-- Prove2me | solution 1 for WorkbookSource.base_23846
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:00:09.550462+00:00
-- url     : https://prove2.me/submissions/31f3f075-b740-4556-80cf-a2283336b6a9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 2 * (b / (2 * b + a) + a / (2 * a + c) + c / (2 * c + b)) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b + 4*a^4*c + a^3*b*c - 2*a^3*c^2 - 2*a^2*b^3 - 5*a^2*b^2*c - 5*a^2*b*c^2 + 4*a*b^4 + a*b^3*c - 5*a*b^2*c^2 + a*b*c^3 + 2*a*c^4 + 2*b^4*c - 2*b^2*c^3 + 4*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^3 * (b - a)^2 + (21 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (21 : ℝ) * a^3 * (c - b)^2 + (40 : ℝ) * a^2 * (b - a)^3 + (63 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (69 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (23 : ℝ) * a^2 * (c - b)^3 + (23 : ℝ) * a^1 * (b - a)^4 + (50 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (64 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (37 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * (b - a)^5 + (12 : ℝ) * (b - a)^4 * (c - b)^1 + (18 : ℝ) * (b - a)^3 * (c - b)^2 + (14 : ℝ) * (b - a)^2 * (c - b)^3 + (4 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^4*b + 4*a^4*c + a^3*b*c - 2*a^3*c^2 - 2*a^2*b^3 - 5*a^2*b^2*c - 5*a^2*b*c^2 + 4*a*b^4 + a*b^3*c - 5*a*b^2*c^2 + a*b*c^3 + 2*a*c^4 + 2*b^4*c - 2*b^2*c^3 + 4*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^3 * (c - a)^2 + (21 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (21 : ℝ) * a^3 * (b - c)^2 + (40 : ℝ) * a^2 * (c - a)^3 + (57 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (63 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (23 : ℝ) * a^2 * (b - c)^3 + (23 : ℝ) * a^1 * (c - a)^4 + (42 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (52 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (33 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (6 : ℝ) * a^1 * (b - c)^4 + (4 : ℝ) * (c - a)^5 + (8 : ℝ) * (c - a)^4 * (b - c)^1 + (10 : ℝ) * (c - a)^3 * (b - c)^2 + (8 : ℝ) * (c - a)^2 * (b - c)^3 + (2 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b + 4*a^4*c + a^3*b*c - 2*a^3*c^2 - 2*a^2*b^3 - 5*a^2*b^2*c - 5*a^2*b*c^2 + 4*a*b^4 + a*b^3*c - 5*a*b^2*c^2 + a*b*c^3 + 2*a*c^4 + 2*b^4*c - 2*b^2*c^3 + 4*b*c^4) := by
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
  have hn : 0 ≤ (2*a^4*b + 4*a^4*c + a^3*b*c - 2*a^3*c^2 - 2*a^2*b^3 - 5*a^2*b^2*c - 5*a^2*b*c^2 + 4*a*b^4 + a*b^3*c - 5*a*b^2*c^2 + a*b*c^3 + 2*a*c^4 + 2*b^4*c - 2*b^2*c^3 + 4*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 2 * (b / (2 * b + a) + a / (2 * a + c) + c / (2 * c + b)) ≥ 3) := @solution
#print axioms solution
