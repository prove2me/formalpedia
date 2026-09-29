-- Prove2me | solution 1 for WorkbookSource.plus_22503
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:33:48.363028+00:00
-- url     : https://prove2.me/submissions/80a21b20-a6c5-4183-9b49-89475ca8f514

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 4 * a * b + b^2) / (a + b + a * b) + (b^2 + 4 * b * c + c^2) / (b + c + b * c) + (c^2 + 4 * c * a + a^2) / (c + a + c * a) ≤ 6   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2/9 + a^4*c^2/9 + 2*a^3*b^3/9 + 2*a^3*b^2*c/9 + 2*a^3*b*c^2/9 + 2*a^3*c^3/9 + a^2*b^4/9 + 2*a^2*b^3*c/9 - 8*a^2*b^2*c^2/3 + 2*a^2*b*c^3/9 + a^2*c^4/9 + 2*a*b^3*c^2/9 + 2*a*b^2*c^3/9 + b^4*c^2/9 + 2*b^3*c^3/9 + b^2*c^4/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2 : ℝ) * a^4 * (b - a)^2 + (2 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2 : ℝ) * a^4 * (c - b)^2 + (56/9 : ℝ) * a^3 * (b - a)^3 + (28/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (20/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (16/9 : ℝ) * a^3 * (c - b)^3 + (62/9 : ℝ) * a^2 * (b - a)^4 + (124/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (10 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (28/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2/9 : ℝ) * a^2 * (c - b)^4 + (28/9 : ℝ) * a^1 * (b - a)^5 + (70/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (20/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (20/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/9 : ℝ) * (b - a)^6 + (4/3 : ℝ) * (b - a)^5 * (c - b)^1 + (13/9 : ℝ) * (b - a)^4 * (c - b)^2 + (2/3 : ℝ) * (b - a)^3 * (c - b)^3 + (1/9 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2/9 + a^4*c^2/9 + 2*a^3*b^3/9 + 2*a^3*b^2*c/9 + 2*a^3*b*c^2/9 + 2*a^3*c^3/9 + a^2*b^4/9 + 2*a^2*b^3*c/9 - 8*a^2*b^2*c^2/3 + 2*a^2*b*c^3/9 + a^2*c^4/9 + 2*a*b^3*c^2/9 + 2*a*b^2*c^3/9 + b^4*c^2/9 + 2*b^3*c^3/9 + b^2*c^4/9) := by
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
  have he : (-a^3*b^2*c - a^3*b^2 - a^3*b*c^2 - 4*a^3*b*c - 2*a^3*b - a^3*c^2 - 2*a^3*c - a^2*b^3*c - a^2*b^3 - 6*a^2*b^2*c^2 - 6*a^2*b^2*c - a^2*b*c^3 - 6*a^2*b*c^2 + 4*a^2*b*c + 6*a^2*b - a^2*c^3 + 6*a^2*c - a*b^3*c^2 - 4*a*b^3*c - 2*a*b^3 - a*b^2*c^3 - 6*a*b^2*c^2 + 4*a*b^2*c + 6*a*b^2 - 4*a*b*c^3 + 4*a*b*c^2 + 12*a*b*c - 2*a*c^3 + 6*a*c^2 - b^3*c^2 - 2*b^3*c - b^2*c^3 + 6*b^2*c - 2*b*c^3 + 6*b*c^2) = (a^4*b^2/9 + a^4*c^2/9 + 2*a^3*b^3/9 + 2*a^3*b^2*c/9 + 2*a^3*b*c^2/9 + 2*a^3*c^3/9 + a^2*b^4/9 + 2*a^2*b^3*c/9 - 8*a^2*b^2*c^2/3 + 2*a^2*b*c^3/9 + a^2*c^4/9 + 2*a*b^3*c^2/9 + 2*a*b^2*c^3/9 + b^4*c^2/9 + 2*b^3*c^3/9 + b^2*c^4/9) := by
    linear_combination (-a^3*b^2/9 - a^3*c^2/9 - a^2*b^3/9 - 10*a^2*b^2*c/9 - 4*a^2*b^2/3 - 10*a^2*b*c^2/9 - 4*a^2*b*c - 2*a^2*b - a^2*c^3/9 - 4*a^2*c^2/3 - 2*a^2*c - 10*a*b^2*c^2/9 - 4*a*b^2*c - 2*a*b^2 - 4*a*b*c^2 - 4*a*b*c - 2*a*c^2 - b^3*c^2/9 - b^2*c^3/9 - 4*b^2*c^2/3 - 2*b^2*c - 2*b*c^2) * habc
  have hn : 0 ≤ (-a^3*b^2*c - a^3*b^2 - a^3*b*c^2 - 4*a^3*b*c - 2*a^3*b - a^3*c^2 - 2*a^3*c - a^2*b^3*c - a^2*b^3 - 6*a^2*b^2*c^2 - 6*a^2*b^2*c - a^2*b*c^3 - 6*a^2*b*c^2 + 4*a^2*b*c + 6*a^2*b - a^2*c^3 + 6*a^2*c - a*b^3*c^2 - 4*a*b^3*c - 2*a*b^3 - a*b^2*c^3 - 6*a*b^2*c^2 + 4*a*b^2*c + 6*a*b^2 - 4*a*b*c^3 + 4*a*b*c^2 + 12*a*b*c - 2*a*c^3 + 6*a*c^2 - b^3*c^2 - 2*b^3*c - b^2*c^3 + 6*b^2*c - 2*b*c^3 + 6*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 + 4 * a * b + b^2) / (a + b + a * b) + (b^2 + 4 * b * c + c^2) / (b + c + b * c) + (c^2 + 4 * c * a + a^2) / (c + a + c * a) ≤ 6) := @solution
#print axioms solution
