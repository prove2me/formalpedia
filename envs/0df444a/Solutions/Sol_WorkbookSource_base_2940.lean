-- Prove2me | solution 1 for WorkbookSource.base_2940
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:03:18.352549+00:00
-- url     : https://prove2.me/submissions/9110e7a7-670b-4492-824e-ad3a8aa50596

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≤ 1 / 3 * (a + b + c) / (a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b*c + 4*a^4*b^3 - 4*a^4*b^2*c - 4*a^4*b*c^2 + 4*a^4*c^3 + 4*a^3*b^4 - 8*a^3*b^3*c + 6*a^3*b^2*c^2 - 8*a^3*b*c^3 + 4*a^3*c^4 - 4*a^2*b^4*c + 6*a^2*b^3*c^2 + 6*a^2*b^2*c^3 - 4*a^2*b*c^4 + 2*a*b^5*c - 4*a*b^4*c^2 - 8*a*b^3*c^3 - 4*a*b^2*c^4 + 2*a*b*c^5 + 4*b^4*c^3 + 4*b^3*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * a^5 * (b - a)^2 + (18 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (18 : ℝ) * a^5 * (c - b)^2 + (72 : ℝ) * a^4 * (b - a)^3 + (108 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (72 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^4 * (c - b)^3 + (118 : ℝ) * a^3 * (b - a)^4 + (236 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (174 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (56 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (10 : ℝ) * a^3 * (c - b)^4 + (100 : ℝ) * a^2 * (b - a)^5 + (250 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (232 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (98 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (20 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^2 * (c - b)^5 + (44 : ℝ) * a^1 * (b - a)^6 + (132 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (148 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (76 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (18 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (8 : ℝ) * (b - a)^7 + (28 : ℝ) * (b - a)^6 * (c - b)^1 + (36 : ℝ) * (b - a)^5 * (c - b)^2 + (20 : ℝ) * (b - a)^4 * (c - b)^3 + (4 : ℝ) * (b - a)^3 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b*c + 4*a^4*b^3 - 4*a^4*b^2*c - 4*a^4*b*c^2 + 4*a^4*c^3 + 4*a^3*b^4 - 8*a^3*b^3*c + 6*a^3*b^2*c^2 - 8*a^3*b*c^3 + 4*a^3*c^4 - 4*a^2*b^4*c + 6*a^2*b^3*c^2 + 6*a^2*b^2*c^3 - 4*a^2*b*c^4 + 2*a*b^5*c - 4*a*b^4*c^2 - 8*a*b^3*c^3 - 4*a*b^2*c^4 + 2*a*b*c^5 + 4*b^4*c^3 + 4*b^3*c^4) := by
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
  have hn : 0 ≤ (2*(a + b + c)*(a^4*b*c + 2*a^3*b^3 - 3*a^3*b^2*c - 3*a^3*b*c^2 + 2*a^3*c^3 - 3*a^2*b^3*c + 9*a^2*b^2*c^2 - 3*a^2*b*c^3 + a*b^4*c - 3*a*b^3*c^2 - 3*a*b^2*c^3 + a*b*c^4 + 2*b^3*c^3)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≤ 1 / 3 * (a + b + c) / (a * b * c)) := @solution
#print axioms solution
