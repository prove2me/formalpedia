-- Prove2me | solution 1 for WorkbookSource.base_15222
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:00:05.027761+00:00
-- url     : https://prove2.me/submissions/c5c071a1-2ef7-46a1-9bd5-009bdcd789d5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^3 / (b + c) + b^3 / (a + c) + c^3 / (a + b) ≥ 3 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5 + 5*a^4*b/3 + 5*a^4*c/3 - a^3*b^2 - a^3*c^2 - a^2*b^3 - 10*a^2*b^2*c/3 - 10*a^2*b*c^2/3 - a^2*c^3 + 5*a*b^4/3 - 10*a*b^2*c^2/3 + 5*a*c^4/3 + 2*b^5 + 5*b^4*c/3 - b^3*c^2 - b^2*c^3 + 5*b*c^4/3 + 2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (76/3 : ℝ) * a^3 * (b - a)^2 + (76/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (76/3 : ℝ) * a^3 * (c - b)^2 + (134/3 : ℝ) * a^2 * (b - a)^3 + (67 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (85 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (94/3 : ℝ) * a^2 * (c - b)^3 + (80/3 : ℝ) * a^1 * (b - a)^4 + (160/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (254/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (58 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (40/3 : ℝ) * a^1 * (c - b)^4 + (16/3 : ℝ) * (b - a)^5 + (40/3 : ℝ) * (b - a)^4 * (c - b)^1 + (26 : ℝ) * (b - a)^3 * (c - b)^2 + (77/3 : ℝ) * (b - a)^2 * (c - b)^3 + (35/3 : ℝ) * (b - a)^1 * (c - b)^4 + (2 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5 + 5*a^4*b/3 + 5*a^4*c/3 - a^3*b^2 - a^3*c^2 - a^2*b^3 - 10*a^2*b^2*c/3 - 10*a^2*b*c^2/3 - a^2*c^3 + 5*a*b^4/3 - 10*a*b^2*c^2/3 + 5*a*c^4/3 + 2*b^5 + 5*b^4*c/3 - b^3*c^2 - b^2*c^3 + 5*b*c^4/3 + 2*c^5) := by
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
  have he : (2*a^5 + 2*a^4*b + 2*a^4*c + 2*a^3*b*c - 3*a^2*b - 3*a^2*c + 2*a*b^4 + 2*a*b^3*c - 3*a*b^2 + 2*a*b*c^3 - 6*a*b*c + 2*a*c^4 - 3*a*c^2 + 2*b^5 + 2*b^4*c - 3*b^2*c + 2*b*c^4 - 3*b*c^2 + 2*c^5) = (2*a^5 + 5*a^4*b/3 + 5*a^4*c/3 - a^3*b^2 - a^3*c^2 - a^2*b^3 - 10*a^2*b^2*c/3 - 10*a^2*b*c^2/3 - a^2*c^3 + 5*a*b^4/3 - 10*a*b^2*c^2/3 + 5*a*c^4/3 + 2*b^5 + 5*b^4*c/3 - b^3*c^2 - b^2*c^3 + 5*b*c^4/3 + 2*c^5) := by
    linear_combination (a^3*b/3 + a^3*c/3 + 2*a^2*b^2/3 + 4*a^2*b*c/3 + a^2*b + 2*a^2*c^2/3 + a^2*c + a*b^3/3 + 4*a*b^2*c/3 + a*b^2 + 4*a*b*c^2/3 + 2*a*b*c + a*c^3/3 + a*c^2 + b^3*c/3 + 2*b^2*c^2/3 + b^2*c + b*c^3/3 + b*c^2) * hab
  have hn : 0 ≤ (2*a^5 + 2*a^4*b + 2*a^4*c + 2*a^3*b*c - 3*a^2*b - 3*a^2*c + 2*a*b^4 + 2*a*b^3*c - 3*a*b^2 + 2*a*b*c^3 - 6*a*b*c + 2*a*c^4 - 3*a*c^2 + 2*b^5 + 2*b^4*c - 3*b^2*c + 2*b*c^4 - 3*b*c^2 + 2*c^5) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a^3 / (b + c) + b^3 / (a + c) + c^3 / (a + b) ≥ 3 / 2) := @solution
#print axioms solution
