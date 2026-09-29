-- Prove2me | solution 1 for WorkbookSource.plus_7663
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:17.153535+00:00
-- url     : https://prove2.me/submissions/7fdb3b72-c54e-404f-a546-557268cd7437

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : a * b + b * c + c * a + 1 / (a * b * c) ≥ 3 + a * b * c   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6/729 + 2*a^5*b/243 + 2*a^5*c/243 + 5*a^4*b^2/243 - 17*a^4*b*c/243 + 5*a^4*c^2/243 + 20*a^3*b^3/729 + 20*a^3*b^2*c/243 + 20*a^3*b*c^2/243 + 20*a^3*c^3/729 + 5*a^2*b^4/243 + 20*a^2*b^3*c/243 - 44*a^2*b^2*c^2/81 + 20*a^2*b*c^3/243 + 5*a^2*c^4/243 + 2*a*b^5/243 - 17*a*b^4*c/243 + 20*a*b^3*c^2/243 + 20*a*b^2*c^3/243 - 17*a*b*c^4/243 + 2*a*c^5/243 + b^6/729 + 2*b^5*c/243 + 5*b^4*c^2/243 + 20*b^3*c^3/729 + 5*b^2*c^4/243 + 2*b*c^5/243 + c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1/3 : ℝ) * a^4 * (b - a)^2 + (1/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1/3 : ℝ) * a^4 * (c - b)^2 + (28/27 : ℝ) * a^3 * (b - a)^3 + (14/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (10/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (8/27 : ℝ) * a^3 * (c - b)^3 + (32/27 : ℝ) * a^2 * (b - a)^4 + (64/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (16/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (16/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2/27 : ℝ) * a^2 * (c - b)^4 + (46/81 : ℝ) * a^1 * (b - a)^5 + (115/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (106/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (44/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (11/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2/81 : ℝ) * a^1 * (c - b)^5 + (64/729 : ℝ) * (b - a)^6 + (64/243 : ℝ) * (b - a)^5 * (c - b)^1 + (80/243 : ℝ) * (b - a)^4 * (c - b)^2 + (160/729 : ℝ) * (b - a)^3 * (c - b)^3 + (20/243 : ℝ) * (b - a)^2 * (c - b)^4 + (4/243 : ℝ) * (b - a)^1 * (c - b)^5 + (1/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6/729 + 2*a^5*b/243 + 2*a^5*c/243 + 5*a^4*b^2/243 - 17*a^4*b*c/243 + 5*a^4*c^2/243 + 20*a^3*b^3/729 + 20*a^3*b^2*c/243 + 20*a^3*b*c^2/243 + 20*a^3*c^3/729 + 5*a^2*b^4/243 + 20*a^2*b^3*c/243 - 44*a^2*b^2*c^2/81 + 20*a^2*b*c^3/243 + 5*a^2*c^4/243 + 2*a*b^5/243 - 17*a*b^4*c/243 + 20*a*b^3*c^2/243 + 20*a*b^2*c^3/243 - 17*a*b*c^4/243 + 2*a*c^5/243 + b^6/729 + 2*b^5*c/243 + 5*b^4*c^2/243 + 20*b^3*c^3/729 + 5*b^2*c^4/243 + 2*b*c^5/243 + c^6/729) := by
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
  have he : (-a^2*b^2*c^2 + a^2*b^2*c + a^2*b*c^2 + a*b^2*c^2 - 3*a*b*c + 1) = (a^6/729 + 2*a^5*b/243 + 2*a^5*c/243 + 5*a^4*b^2/243 - 17*a^4*b*c/243 + 5*a^4*c^2/243 + 20*a^3*b^3/729 + 20*a^3*b^2*c/243 + 20*a^3*b*c^2/243 + 20*a^3*c^3/729 + 5*a^2*b^4/243 + 20*a^2*b^3*c/243 - 44*a^2*b^2*c^2/81 + 20*a^2*b*c^3/243 + 5*a^2*c^4/243 + 2*a*b^5/243 - 17*a*b^4*c/243 + 20*a*b^3*c^2/243 + 20*a*b^2*c^3/243 - 17*a*b*c^4/243 + 2*a*c^5/243 + b^6/729 + 2*b^5*c/243 + 5*b^4*c^2/243 + 20*b^3*c^3/729 + 5*b^2*c^4/243 + 2*b*c^5/243 + c^6/729) := by
    linear_combination (-a^5/729 - 5*a^4*b/729 - 5*a^4*c/729 - a^4/243 - 10*a^3*b^2/729 + 61*a^3*b*c/729 - 4*a^3*b/243 - 10*a^3*c^2/729 - 4*a^3*c/243 - a^3/81 - 10*a^2*b^3/729 - 37*a^2*b^2*c/243 - 2*a^2*b^2/81 - 37*a^2*b*c^2/243 + 23*a^2*b*c/81 - a^2*b/27 - 10*a^2*c^3/729 - 2*a^2*c^2/81 - a^2*c/27 - a^2/27 - 5*a*b^4/729 + 61*a*b^3*c/729 - 4*a*b^3/243 - 37*a*b^2*c^2/243 + 23*a*b^2*c/81 - a*b^2/27 + 61*a*b*c^3/729 + 23*a*b*c^2/81 + 25*a*b*c/27 - 2*a*b/27 - 5*a*c^4/729 - 4*a*c^3/243 - a*c^2/27 - 2*a*c/27 - a/9 - b^5/729 - 5*b^4*c/729 - b^4/243 - 10*b^3*c^2/729 - 4*b^3*c/243 - b^3/81 - 10*b^2*c^3/729 - 2*b^2*c^2/81 - b^2*c/27 - b^2/27 - 5*b*c^4/729 - 4*b*c^3/243 - b*c^2/27 - 2*b*c/27 - b/9 - c^5/729 - c^4/243 - c^3/81 - c^2/27 - c/9 - 1/3) * habc
  have hn : 0 ≤ (-a^2*b^2*c^2 + a^2*b^2*c + a^2*b*c^2 + a*b^2*c^2 - 3*a*b*c + 1) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3), a * b + b * c + c * a + 1 / (a * b * c) ≥ 3 + a * b * c) := @solution
#print axioms solution
