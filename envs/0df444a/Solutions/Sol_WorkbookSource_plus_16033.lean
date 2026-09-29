-- Prove2me | solution 1 for WorkbookSource.plus_16033
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:16:56.492701+00:00
-- url     : https://prove2.me/submissions/176ce049-32f5-4a35-b39a-cb1af691829b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (1 + b / a) * (1 + c / a) + (1 + c / b) * (1 + a / b) + (1 + a / c) * (1 + b / c) + 2 * (b * c / a ^ 2 + c * a / b ^ 2 + a * b / c ^ 2) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b^3/3 + a^5*b^2*c/9 + a^5*b*c^2/9 + a^5*c^3/3 + 2*a^4*b^4/3 + a^4*b^3*c - 47*a^4*b^2*c^2/9 + a^4*b*c^3 + 2*a^4*c^4/3 + a^3*b^5/3 + a^3*b^4*c + 5*a^3*b^3*c^2/3 + 5*a^3*b^2*c^3/3 + a^3*b*c^4 + a^3*c^5/3 + a^2*b^5*c/9 - 47*a^2*b^4*c^2/9 + 5*a^2*b^3*c^3/3 - 47*a^2*b^2*c^4/9 + a^2*b*c^5/9 + a*b^5*c^2/9 + a*b^4*c^3 + a*b^3*c^4 + a*b^2*c^5/9 + b^5*c^3/3 + 2*b^4*c^4/3 + b^3*c^5/3) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * a^6 * (b - a)^2 + (7 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (7 : ℝ) * a^6 * (c - b)^2 + (104/3 : ℝ) * a^5 * (b - a)^3 + (52 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (32 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (22/3 : ℝ) * a^5 * (c - b)^3 + (638/9 : ℝ) * a^4 * (b - a)^4 + (1276/9 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (283/3 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (211/9 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (23/9 : ℝ) * a^4 * (c - b)^4 + (76 : ℝ) * a^3 * (b - a)^5 + (190 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1468/9 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (164/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (22/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (8/9 : ℝ) * a^3 * (c - b)^5 + (133/3 : ℝ) * a^2 * (b - a)^6 + (133 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (437/3 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (209/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (14 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (4/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (116/9 : ℝ) * a^1 * (b - a)^7 + (406/9 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (542/9 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (340/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (98/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (10/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (4/3 : ℝ) * (b - a)^8 + (16/3 : ℝ) * (b - a)^7 * (c - b)^1 + (25/3 : ℝ) * (b - a)^6 * (c - b)^2 + (19/3 : ℝ) * (b - a)^5 * (c - b)^3 + (7/3 : ℝ) * (b - a)^4 * (c - b)^4 + (1/3 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b^3/3 + a^5*b^2*c/9 + a^5*b*c^2/9 + a^5*c^3/3 + 2*a^4*b^4/3 + a^4*b^3*c - 47*a^4*b^2*c^2/9 + a^4*b*c^3 + 2*a^4*c^4/3 + a^3*b^5/3 + a^3*b^4*c + 5*a^3*b^3*c^2/3 + 5*a^3*b^2*c^3/3 + a^3*b*c^4 + a^3*c^5/3 + a^2*b^5*c/9 - 47*a^2*b^4*c^2/9 + 5*a^2*b^3*c^3/3 - 47*a^2*b^2*c^4/9 + a^2*b*c^5/9 + a*b^5*c^2/9 + a*b^4*c^3 + a*b^3*c^4 + a*b^2*c^5/9 + b^5*c^3/3 + 2*b^4*c^4/3 + b^3*c^5/3) := by
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
  have he : (-6*a^4*b^2*c^2 + 3*a^3*b^3 + a^3*b^2*c + a^3*b*c^2 + 3*a^3*c^3 - 6*a^2*b^4*c^2 + a^2*b^3*c - 6*a^2*b^2*c^4 + 3*a^2*b^2*c^2 + a^2*b*c^3 + a*b^3*c^2 + a*b^2*c^3 + 3*b^3*c^3) = (a^5*b^3/3 + a^5*b^2*c/9 + a^5*b*c^2/9 + a^5*c^3/3 + 2*a^4*b^4/3 + a^4*b^3*c - 47*a^4*b^2*c^2/9 + a^4*b*c^3 + 2*a^4*c^4/3 + a^3*b^5/3 + a^3*b^4*c + 5*a^3*b^3*c^2/3 + 5*a^3*b^2*c^3/3 + a^3*b*c^4 + a^3*c^5/3 + a^2*b^5*c/9 - 47*a^2*b^4*c^2/9 + 5*a^2*b^3*c^3/3 - 47*a^2*b^2*c^4/9 + a^2*b*c^5/9 + a*b^5*c^2/9 + a*b^4*c^3 + a*b^3*c^4 + a*b^2*c^5/9 + b^5*c^3/3 + 2*b^4*c^4/3 + b^3*c^5/3) := by
    linear_combination (-a^4*b^3/3 - a^4*b^2*c/9 - a^4*b*c^2/9 - a^4*c^3/3 - a^3*b^4/3 - 5*a^3*b^3*c/9 - a^3*b^3 - 5*a^3*b^2*c^2/9 - a^3*b^2*c/3 - 5*a^3*b*c^3/9 - a^3*b*c^2/3 - a^3*c^4/3 - a^3*c^3 - a^2*b^4*c/9 - 5*a^2*b^3*c^2/9 - a^2*b^3*c/3 - 5*a^2*b^2*c^3/9 - a^2*b^2*c^2 - a^2*b*c^4/9 - a^2*b*c^3/3 - a*b^4*c^2/9 - 5*a*b^3*c^3/9 - a*b^3*c^2/3 - a*b^2*c^4/9 - a*b^2*c^3/3 - b^4*c^3/3 - b^3*c^4/3 - b^3*c^3) * habc
  have hn : 0 ≤ (-6*a^4*b^2*c^2 + 3*a^3*b^3 + a^3*b^2*c + a^3*b*c^2 + 3*a^3*c^3 - 6*a^2*b^4*c^2 + a^2*b^3*c - 6*a^2*b^2*c^4 + 3*a^2*b^2*c^2 + a^2*b*c^3 + a*b^3*c^2 + a*b^2*c^3 + 3*b^3*c^3) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (1 + b / a) * (1 + c / a) + (1 + c / b) * (1 + a / b) + (1 + a / c) * (1 + b / c) + 2 * (b * c / a ^ 2 + c * a / b ^ 2 + a * b / c ^ 2) ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2)) := @solution
#print axioms solution
