-- Prove2me | solution 1 for WorkbookSource.base_33362
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:55:30.727875+00:00
-- url     : https://prove2.me/submissions/76ef83ac-cb77-4483-b5b1-a4e09447b76a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + (1 / 8) * ((a + b) * (b + c) * (c + a)) / (a^3 + b^3 + c^3) ≥ 4 / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (24*a^5 - 32*a^4*b - 32*a^4*c + 27*a^3*b^2 - 26*a^3*b*c + 27*a^3*c^2 + 27*a^2*b^3 + 12*a^2*b^2*c + 12*a^2*b*c^2 + 27*a^2*c^3 - 32*a*b^4 - 26*a*b^3*c + 12*a*b^2*c^2 - 26*a*b*c^3 - 32*a*c^4 + 24*b^5 - 32*b^4*c + 27*b^3*c^2 + 27*b^2*c^3 - 32*b*c^4 + 24*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * a^3 * (b - a)^2 + (18 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (18 : ℝ) * a^3 * (c - b)^2 + (42 : ℝ) * a^2 * (b - a)^3 + (63 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^2 * (c - b)^3 + (86 : ℝ) * a^1 * (b - a)^4 + (172 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (210 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (124 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (56 : ℝ) * a^1 * (c - b)^4 + (38 : ℝ) * (b - a)^5 + (95 : ℝ) * (b - a)^4 * (c - b)^1 + (156 : ℝ) * (b - a)^3 * (c - b)^2 + (139 : ℝ) * (b - a)^2 * (c - b)^3 + (88 : ℝ) * (b - a)^1 * (c - b)^4 + (24 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (24*a^5 - 32*a^4*b - 32*a^4*c + 27*a^3*b^2 - 26*a^3*b*c + 27*a^3*c^2 + 27*a^2*b^3 + 12*a^2*b^2*c + 12*a^2*b*c^2 + 27*a^2*c^3 - 32*a*b^4 - 26*a*b^3*c + 12*a*b^2*c^2 - 26*a*b*c^3 - 32*a*c^4 + 24*b^5 - 32*b^4*c + 27*b^3*c^2 + 27*b^2*c^3 - 32*b*c^4 + 24*c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (24*a^5 - 32*a^4*b - 32*a^4*c + 27*a^3*b^2 - 26*a^3*b*c + 27*a^3*c^2 + 27*a^2*b^3 + 12*a^2*b^2*c + 12*a^2*b*c^2 + 27*a^2*c^3 - 32*a*b^4 - 26*a*b^3*c + 12*a*b^2*c^2 - 26*a*b*c^3 - 32*a*c^4 + 24*b^5 - 32*b^4*c + 27*b^3*c^2 + 27*b^2*c^3 - 32*b*c^4 + 24*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + (1 / 8) * ((a + b) * (b + c) * (c + a)) / (a^3 + b^3 + c^3) ≥ 4 / 3) := @solution
#print axioms solution
