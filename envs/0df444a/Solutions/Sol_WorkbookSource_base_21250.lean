-- Prove2me | solution 1 for WorkbookSource.base_21250
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:10.161986+00:00
-- url     : https://prove2.me/submissions/1ad4c471-69a1-4a2a-881f-9d927d8df941

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) ^ 2 / (3 * a * b * c * (a + b + c)) + a * b * c / (a + b + c) ^ 3 ≥ 28 / 27  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^4*b^2 - 10*a^4*b*c + 9*a^4*c^2 + 18*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 18*a^3*c^3 + 9*a^2*b^4 - 12*a^2*b^3*c - 6*a^2*b^2*c^2 - 12*a^2*b*c^3 + 9*a^2*c^4 - 10*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 10*a*b*c^4 + 9*b^4*c^2 + 18*b^3*c^3 + 9*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^4 * (b - a)^2 + (72 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (72 : ℝ) * a^4 * (c - b)^2 + (244 : ℝ) * a^3 * (b - a)^3 + (366 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (210 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (44 : ℝ) * a^3 * (c - b)^3 + (308 : ℝ) * a^2 * (b - a)^4 + (616 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (390 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (82 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^2 * (c - b)^4 + (172 : ℝ) * a^1 * (b - a)^5 + (430 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (360 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (110 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (36 : ℝ) * (b - a)^6 + (108 : ℝ) * (b - a)^5 * (c - b)^1 + (117 : ℝ) * (b - a)^4 * (c - b)^2 + (54 : ℝ) * (b - a)^3 * (c - b)^3 + (9 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^4*b^2 - 10*a^4*b*c + 9*a^4*c^2 + 18*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 18*a^3*c^3 + 9*a^2*b^4 - 12*a^2*b^3*c - 6*a^2*b^2*c^2 - 12*a^2*b*c^3 + 9*a^2*c^4 - 10*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 10*a*b*c^4 + 9*b^4*c^2 + 18*b^3*c^3 + 9*b^2*c^4) := by
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
  have hn : 0 ≤ (9*a^4*b^2 - 10*a^4*b*c + 9*a^4*c^2 + 18*a^3*b^3 - 12*a^3*b^2*c - 12*a^3*b*c^2 + 18*a^3*c^3 + 9*a^2*b^4 - 12*a^2*b^3*c - 6*a^2*b^2*c^2 - 12*a^2*b*c^3 + 9*a^2*c^4 - 10*a*b^4*c - 12*a*b^3*c^2 - 12*a*b^2*c^3 - 10*a*b*c^4 + 9*b^4*c^2 + 18*b^3*c^3 + 9*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a * b + b * c + c * a) ^ 2 / (3 * a * b * c * (a + b + c)) + a * b * c / (a + b + c) ^ 3 ≥ 28 / 27) := @solution
#print axioms solution
