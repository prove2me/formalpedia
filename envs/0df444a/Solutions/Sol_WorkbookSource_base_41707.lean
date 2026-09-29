-- Prove2me | solution 1 for WorkbookSource.base_41707
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:20.396466+00:00
-- url     : https://prove2.me/submissions/3acc0d23-872a-45e8-b323-cb6ca5116efc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2 + a * b + b * c + c * a)^3 ≥ 24 * (a^2 * b + b^2 * c + c^2 * a) * (b^2 * a + c^2 * b + a^2 * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 3*a^5*b + 3*a^5*c + 6*a^4*b^2 - 15*a^4*b*c + 6*a^4*c^2 - 17*a^3*b^3 + 15*a^3*b^2*c + 15*a^3*b*c^2 - 17*a^3*c^3 + 6*a^2*b^4 + 15*a^2*b^3*c - 51*a^2*b^2*c^2 + 15*a^2*b*c^3 + 6*a^2*c^4 + 3*a*b^5 - 15*a*b^4*c + 15*a*b^3*c^2 + 15*a*b^2*c^3 - 15*a*b*c^4 + 3*a*c^5 + b^6 + 3*b^5*c + 6*b^4*c^2 - 17*b^3*c^3 + 6*b^2*c^4 + 3*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (36 : ℝ) * a^4 * (b - a)^2 + (36 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (36 : ℝ) * a^4 * (c - b)^2 + (80 : ℝ) * a^3 * (b - a)^3 + (120 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (168 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (64 : ℝ) * a^3 * (c - b)^3 + (66 : ℝ) * a^2 * (b - a)^4 + (132 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (246 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (180 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (42 : ℝ) * a^2 * (c - b)^4 + (24 : ℝ) * a^1 * (b - a)^5 + (60 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (144 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (156 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (72 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^1 * (c - b)^5 + (3 : ℝ) * (b - a)^6 + (9 : ℝ) * (b - a)^5 * (c - b)^1 + (36 : ℝ) * (b - a)^4 * (c - b)^2 + (57 : ℝ) * (b - a)^3 * (c - b)^3 + (36 : ℝ) * (b - a)^2 * (c - b)^4 + (9 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 3*a^5*b + 3*a^5*c + 6*a^4*b^2 - 15*a^4*b*c + 6*a^4*c^2 - 17*a^3*b^3 + 15*a^3*b^2*c + 15*a^3*b*c^2 - 17*a^3*c^3 + 6*a^2*b^4 + 15*a^2*b^3*c - 51*a^2*b^2*c^2 + 15*a^2*b*c^3 + 6*a^2*c^4 + 3*a*b^5 - 15*a*b^4*c + 15*a*b^3*c^2 + 15*a*b^2*c^3 - 15*a*b*c^4 + 3*a*c^5 + b^6 + 3*b^5*c + 6*b^4*c^2 - 17*b^3*c^3 + 6*b^2*c^4 + 3*b*c^5 + c^6) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2 + a * b + b * c + c * a)^3 ≥ 24 * (a^2 * b + b^2 * c + c^2 * a) * (b^2 * a + c^2 * b + a^2 * c)) := @solution
#print axioms solution
