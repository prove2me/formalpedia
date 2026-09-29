-- Prove2me | solution 1 for WorkbookSource.plus_25937
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:51:24.318954+00:00
-- url     : https://prove2.me/submissions/c8f45b08-7a35-4d5f-a48c-8bf312c4a4aa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (2 * a + b * c) + 1 / (2 * b + c * a) + 1 / (2 * c + a * b) ≤ 1 / (a * b * c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*b^2/27 + 26*a^5*b*c/81 + 4*a^5*c^2/27 + 4*a^4*b^3/9 + 14*a^4*b^2*c/81 + 14*a^4*b*c^2/81 + 4*a^4*c^3/9 + 4*a^3*b^4/9 - 8*a^3*b^3*c/27 - 14*a^3*b^2*c^2/9 - 8*a^3*b*c^3/27 + 4*a^3*c^4/9 + 4*a^2*b^5/27 + 14*a^2*b^4*c/81 - 14*a^2*b^3*c^2/9 - 14*a^2*b^2*c^3/9 + 14*a^2*b*c^4/81 + 4*a^2*c^5/27 + 26*a*b^5*c/81 + 14*a*b^4*c^2/81 - 8*a*b^3*c^3/27 + 14*a*b^2*c^4/81 + 26*a*b*c^5/81 + 4*b^5*c^2/27 + 4*b^4*c^3/9 + 4*b^3*c^4/9 + 4*b^2*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (22/3 : ℝ) * a^5 * (b - a)^2 + (22/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (22/3 : ℝ) * a^5 * (c - b)^2 + (724/27 : ℝ) * a^4 * (b - a)^3 + (362/9 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (298/9 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (266/27 : ℝ) * a^4 * (c - b)^3 + (3098/81 : ℝ) * a^3 * (b - a)^4 + (6196/81 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (1798/27 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (2296/81 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (350/81 : ℝ) * a^3 * (c - b)^4 + (2152/81 : ℝ) * a^2 * (b - a)^5 + (5380/81 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (5404/81 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (2726/81 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (650/81 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (50/81 : ℝ) * a^2 * (c - b)^5 + (728/81 : ℝ) * a^1 * (b - a)^6 + (728/27 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (2566/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (1492/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (16/3 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (50/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (32/27 : ℝ) * (b - a)^7 + (112/27 : ℝ) * (b - a)^6 * (c - b)^1 + (152/27 : ℝ) * (b - a)^5 * (c - b)^2 + (100/27 : ℝ) * (b - a)^4 * (c - b)^3 + (32/27 : ℝ) * (b - a)^3 * (c - b)^4 + (4/27 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*b^2/27 + 26*a^5*b*c/81 + 4*a^5*c^2/27 + 4*a^4*b^3/9 + 14*a^4*b^2*c/81 + 14*a^4*b*c^2/81 + 4*a^4*c^3/9 + 4*a^3*b^4/9 - 8*a^3*b^3*c/27 - 14*a^3*b^2*c^2/9 - 8*a^3*b*c^3/27 + 4*a^3*c^4/9 + 4*a^2*b^5/27 + 14*a^2*b^4*c/81 - 14*a^2*b^3*c^2/9 - 14*a^2*b^2*c^3/9 + 14*a^2*b*c^4/81 + 4*a^2*c^5/27 + 26*a*b^5*c/81 + 14*a*b^4*c^2/81 - 8*a*b^3*c^3/27 + 14*a*b^2*c^4/81 + 26*a*b*c^5/81 + 4*b^5*c^2/27 + 4*b^4*c^3/9 + 4*b^3*c^4/9 + 4*b^2*c^5/27) := by
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
  have he : (-a^3*b^2*c^2 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 2*a^3*b*c - a^2*b^3*c^2 - 2*a^2*b^3*c - a^2*b^2*c^3 + a^2*b^2*c^2 - 4*a^2*b^2*c + 4*a^2*b^2 - 2*a^2*b*c^3 - 4*a^2*b*c^2 + 4*a^2*c^2 - 2*a*b^3*c^2 + 2*a*b^3*c - 2*a*b^2*c^3 - 4*a*b^2*c^2 + 2*a*b*c^3 + 8*a*b*c + 4*b^2*c^2) = (4*a^5*b^2/27 + 26*a^5*b*c/81 + 4*a^5*c^2/27 + 4*a^4*b^3/9 + 14*a^4*b^2*c/81 + 14*a^4*b*c^2/81 + 4*a^4*c^3/9 + 4*a^3*b^4/9 - 8*a^3*b^3*c/27 - 14*a^3*b^2*c^2/9 - 8*a^3*b*c^3/27 + 4*a^3*c^4/9 + 4*a^2*b^5/27 + 14*a^2*b^4*c/81 - 14*a^2*b^3*c^2/9 - 14*a^2*b^2*c^3/9 + 14*a^2*b*c^4/81 + 4*a^2*c^5/27 + 26*a*b^5*c/81 + 14*a*b^4*c^2/81 - 8*a*b^3*c^3/27 + 14*a*b^2*c^4/81 + 26*a*b*c^5/81 + 4*b^5*c^2/27 + 4*b^4*c^3/9 + 4*b^3*c^4/9 + 4*b^2*c^5/27) := by
    linear_combination (-4*a^4*b^2/27 - 26*a^4*b*c/81 - 4*a^4*c^2/27 - 8*a^3*b^3/27 + 8*a^3*b^2*c/27 - 4*a^3*b^2/9 + 8*a^3*b*c^2/27 - 26*a^3*b*c/27 - 8*a^3*c^3/27 - 4*a^3*c^2/9 - 4*a^2*b^4/27 + 8*a^2*b^3*c/27 - 4*a^2*b^3/9 - a^2*b^2*c^2/27 + 8*a^2*b^2*c/27 - 4*a^2*b^2/3 + 8*a^2*b*c^3/27 + 8*a^2*b*c^2/27 - 8*a^2*b*c/9 - 4*a^2*c^4/27 - 4*a^2*c^3/9 - 4*a^2*c^2/3 - 26*a*b^4*c/81 + 8*a*b^3*c^2/27 - 26*a*b^3*c/27 + 8*a*b^2*c^3/27 + 8*a*b^2*c^2/27 - 8*a*b^2*c/9 - 26*a*b*c^4/81 - 26*a*b*c^3/27 - 8*a*b*c^2/9 - 8*a*b*c/3 - 4*b^4*c^2/27 - 8*b^3*c^3/27 - 4*b^3*c^2/9 - 4*b^2*c^4/27 - 4*b^2*c^3/9 - 4*b^2*c^2/3) * habc
  have hn : 0 ≤ (-a^3*b^2*c^2 - 2*a^3*b^2*c - 2*a^3*b*c^2 + 2*a^3*b*c - a^2*b^3*c^2 - 2*a^2*b^3*c - a^2*b^2*c^3 + a^2*b^2*c^2 - 4*a^2*b^2*c + 4*a^2*b^2 - 2*a^2*b*c^3 - 4*a^2*b*c^2 + 4*a^2*c^2 - 2*a*b^3*c^2 + 2*a*b^3*c - 2*a*b^2*c^3 - 4*a*b^2*c^2 + 2*a*b*c^3 + 8*a*b*c + 4*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 1 / (2 * a + b * c) + 1 / (2 * b + c * a) + 1 / (2 * c + a * b) ≤ 1 / (a * b * c)) := @solution
#print axioms solution
