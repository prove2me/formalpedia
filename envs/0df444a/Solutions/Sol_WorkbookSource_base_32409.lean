-- Prove2me | solution 1 for WorkbookSource.base_32409
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:36:03.793199+00:00
-- url     : https://prove2.me/submissions/ec36da9c-6146-43c7-a946-2f9b52a926e4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + (9 * a * b * c) / (2 * (a + b + c) * (b * c + c * a + a * b))) ≥ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b + 2*a^5*c + 2*a^4*b*c - 4*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - 4*a^3*c^3 - a^2*b^3*c - a^2*b*c^3 + 2*a*b^5 + 2*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c - 4*b^3*c^3 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^4 * (b - a)^2 + (20 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (20 : ℝ) * a^4 * (c - b)^2 + (42 : ℝ) * a^3 * (b - a)^3 + (63 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (97 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (38 : ℝ) * a^3 * (c - b)^3 + (28 : ℝ) * a^2 * (b - a)^4 + (56 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (129 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (101 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (22 : ℝ) * a^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^5 + (15 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (60 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (75 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (32 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (8 : ℝ) * (b - a)^4 * (c - b)^2 + (16 : ℝ) * (b - a)^3 * (c - b)^3 + (10 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b + 2*a^5*c + 2*a^4*b*c - 4*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - 4*a^3*c^3 - a^2*b^3*c - a^2*b*c^3 + 2*a*b^5 + 2*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c - 4*b^3*c^3 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*b + 2*a^5*c + 2*a^4*b*c - 4*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - 4*a^3*c^3 - a^2*b^3*c - a^2*b*c^3 + 2*a*b^5 + 2*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c - 4*b^3*c^3 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a) + c / (a + b) + (9 * a * b * c) / (2 * (a + b + c) * (b * c + c * a + a * b))) ≥ 2) := @solution
#print axioms solution
