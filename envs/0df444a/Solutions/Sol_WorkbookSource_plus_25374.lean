-- Prove2me | solution 1 for WorkbookSource.plus_25374
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:30:03.882206+00:00
-- url     : https://prove2.me/submissions/acb8b134-426a-489d-9ed4-b63044b8b44f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (3 * a - b * c) * (3 * b - a * c) * (3 * c - a * b) ≤ 8   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^6/729 + 16*a^5*b/243 + 16*a^5*c/243 + 283*a^4*b^2/243 - 406*a^4*b*c/243 + 283*a^4*c^2/243 + 1618*a^3*b^3/729 - 326*a^3*b^2*c/243 - 326*a^3*b*c^2/243 + 1618*a^3*c^3/729 + 283*a^2*b^4/243 - 326*a^2*b^3*c/243 - 82*a^2*b^2*c^2/81 - 326*a^2*b*c^3/243 + 283*a^2*c^4/243 + 16*a*b^5/243 - 406*a*b^4*c/243 - 326*a*b^3*c^2/243 - 326*a*b^2*c^3/243 - 406*a*b*c^4/243 + 16*a*c^5/243 + 8*b^6/729 + 16*b^5*c/243 + 283*b^4*c^2/243 + 1618*b^3*c^3/729 + 283*b^2*c^4/243 + 16*b*c^5/243 + 8*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (28/3 : ℝ) * a^4 * (b - a)^2 + (28/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (28/3 : ℝ) * a^4 * (c - b)^2 + (848/27 : ℝ) * a^3 * (b - a)^3 + (424/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (248/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (160/27 : ℝ) * a^3 * (c - b)^3 + (1072/27 : ℝ) * a^2 * (b - a)^4 + (2144/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (464/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (320/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (40/27 : ℝ) * a^2 * (c - b)^4 + (1808/81 : ℝ) * a^1 * (b - a)^5 + (4520/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (3872/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1288/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (160/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (16/81 : ℝ) * a^1 * (c - b)^5 + (3428/729 : ℝ) * (b - a)^6 + (3428/243 : ℝ) * (b - a)^5 * (c - b)^1 + (3799/243 : ℝ) * (b - a)^4 * (c - b)^2 + (5654/729 : ℝ) * (b - a)^3 * (c - b)^3 + (403/243 : ℝ) * (b - a)^2 * (c - b)^4 + (32/243 : ℝ) * (b - a)^1 * (c - b)^5 + (8/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^6/729 + 16*a^5*b/243 + 16*a^5*c/243 + 283*a^4*b^2/243 - 406*a^4*b*c/243 + 283*a^4*c^2/243 + 1618*a^3*b^3/729 - 326*a^3*b^2*c/243 - 326*a^3*b*c^2/243 + 1618*a^3*c^3/729 + 283*a^2*b^4/243 - 326*a^2*b^3*c/243 - 82*a^2*b^2*c^2/81 - 326*a^2*b*c^3/243 + 283*a^2*c^4/243 + 16*a*b^5/243 - 406*a*b^4*c/243 - 326*a*b^3*c^2/243 - 326*a*b^2*c^3/243 - 406*a*b*c^4/243 + 16*a*c^5/243 + 8*b^6/729 + 16*b^5*c/243 + 283*b^4*c^2/243 + 1618*b^3*c^3/729 + 283*b^2*c^4/243 + 16*b*c^5/243 + 8*c^6/729) := by
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
  have he : (-3*a^3*b*c + a^2*b^2*c^2 + 9*a^2*b^2 + 9*a^2*c^2 - 3*a*b^3*c - 3*a*b*c^3 - 27*a*b*c + 9*b^2*c^2 + 8) = (8*a^6/729 + 16*a^5*b/243 + 16*a^5*c/243 + 283*a^4*b^2/243 - 406*a^4*b*c/243 + 283*a^4*c^2/243 + 1618*a^3*b^3/729 - 326*a^3*b^2*c/243 - 326*a^3*b*c^2/243 + 1618*a^3*c^3/729 + 283*a^2*b^4/243 - 326*a^2*b^3*c/243 - 82*a^2*b^2*c^2/81 - 326*a^2*b*c^3/243 + 283*a^2*c^4/243 + 16*a*b^5/243 - 406*a*b^4*c/243 - 326*a*b^3*c^2/243 - 326*a*b^2*c^3/243 - 406*a*b*c^4/243 + 16*a*c^5/243 + 8*b^6/729 + 16*b^5*c/243 + 283*b^4*c^2/243 + 1618*b^3*c^3/729 + 283*b^2*c^4/243 + 16*b*c^5/243 + 8*c^6/729) := by
    linear_combination (-8*a^5/729 - 40*a^4*b/729 - 40*a^4*c/729 - 8*a^4/243 - 809*a^3*b^2/729 + 1298*a^3*b*c/729 - 32*a^3*b/243 - 809*a^3*c^2/729 - 32*a^3*c/243 - 8*a^3/81 - 809*a^2*b^3/729 + 163*a^2*b^2*c/243 - 259*a^2*b^2/81 + 163*a^2*b*c^2/243 + 211*a^2*b*c/81 - 8*a^2*b/27 - 809*a^2*c^3/729 - 259*a^2*c^2/81 - 8*a^2*c/27 - 8*a^2/27 - 40*a*b^4/729 + 1298*a*b^3*c/729 - 32*a*b^3/243 + 163*a*b^2*c^2/243 + 211*a*b^2*c/81 - 8*a*b^2/27 + 1298*a*b*c^3/729 + 211*a*b*c^2/81 + 227*a*b*c/27 - 16*a*b/27 - 40*a*c^4/729 - 32*a*c^3/243 - 8*a*c^2/27 - 16*a*c/27 - 8*a/9 - 8*b^5/729 - 40*b^4*c/729 - 8*b^4/243 - 809*b^3*c^2/729 - 32*b^3*c/243 - 8*b^3/81 - 809*b^2*c^3/729 - 259*b^2*c^2/81 - 8*b^2*c/27 - 8*b^2/27 - 40*b*c^4/729 - 32*b*c^3/243 - 8*b*c^2/27 - 16*b*c/27 - 8*b/9 - 8*c^5/729 - 8*c^4/243 - 8*c^3/81 - 8*c^2/27 - 8*c/9 - 8/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), (3 * a - b * c) * (3 * b - a * c) * (3 * c - a * b) ≤ 8) := @solution
#print axioms solution
