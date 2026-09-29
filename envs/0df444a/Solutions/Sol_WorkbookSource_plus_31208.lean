-- Prove2me | solution 1 for WorkbookSource.plus_31208
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:44:33.546881+00:00
-- url     : https://prove2.me/submissions/df2f8a8a-79c9-4b9f-b2f4-6b551ca65076

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) ≤ 3 / (a * b * c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/9 + a^5*c/9 + 4*a^4*b^2/9 - a^4*b*c/9 + 4*a^4*c^2/9 + 2*a^3*b^3/3 - 8*a^3*b^2*c/9 + a^3*b*c^2/9 + 2*a^3*c^3/3 + 4*a^2*b^4/9 + a^2*b^3*c/9 - 8*a^2*b^2*c^2/3 - 8*a^2*b*c^3/9 + 4*a^2*c^4/9 + a*b^5/9 - a*b^4*c/9 - 8*a*b^3*c^2/9 + a*b^2*c^3/9 - a*b*c^4/9 + a*c^5/9 + b^5*c/9 + 4*b^4*c^2/9 + 2*b^3*c^3/3 + 4*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^4 * (b - a)^2 + (6 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (6 : ℝ) * a^4 * (c - b)^2 + (163/9 : ℝ) * a^3 * (b - a)^3 + (83/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (64/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (53/9 : ℝ) * a^3 * (c - b)^3 + (182/9 : ℝ) * a^2 * (b - a)^4 + (373/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (103/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (118/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (17/9 : ℝ) * a^2 * (c - b)^4 + (89/9 : ℝ) * a^1 * (b - a)^5 + (227/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (223/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (103/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (22/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2/9 : ℝ) * a^1 * (c - b)^5 + (16/9 : ℝ) * (b - a)^6 + (16/3 : ℝ) * (b - a)^5 * (c - b)^1 + (56/9 : ℝ) * (b - a)^4 * (c - b)^2 + (32/9 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 + (1/9 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b/9 + a^5*c/9 + 4*a^4*b^2/9 - a^4*b*c/9 + 4*a^4*c^2/9 + 2*a^3*b^3/3 - 8*a^3*b^2*c/9 + a^3*b*c^2/9 + 2*a^3*c^3/3 + 4*a^2*b^4/9 + a^2*b^3*c/9 - 8*a^2*b^2*c^2/3 - 8*a^2*b*c^3/9 + 4*a^2*c^4/9 + a*b^5/9 - a*b^4*c/9 - 8*a*b^3*c^2/9 + a*b^2*c^3/9 - a*b*c^4/9 + a*c^5/9 + b^5*c/9 + 4*b^4*c^2/9 + 2*b^3*c^3/3 + 4*b^2*c^4/9 + b*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (6 : ℝ) * a^4 * (c - a)^2 + (6 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (6 : ℝ) * a^4 * (b - c)^2 + (163/9 : ℝ) * a^3 * (c - a)^3 + (80/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (61/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (53/9 : ℝ) * a^3 * (b - c)^3 + (182/9 : ℝ) * a^2 * (c - a)^4 + (355/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (94/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (109/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (17/9 : ℝ) * a^2 * (b - c)^4 + (89/9 : ℝ) * a^1 * (c - a)^5 + (218/9 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (205/9 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (94/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (22/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2/9 : ℝ) * a^1 * (b - c)^5 + (16/9 : ℝ) * (c - a)^6 + (16/3 : ℝ) * (c - a)^5 * (b - c)^1 + (56/9 : ℝ) * (c - a)^4 * (b - c)^2 + (32/9 : ℝ) * (c - a)^3 * (b - c)^3 + (1 : ℝ) * (c - a)^2 * (b - c)^4 + (1/9 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/9 + a^5*c/9 + 4*a^4*b^2/9 - a^4*b*c/9 + 4*a^4*c^2/9 + 2*a^3*b^3/3 - 8*a^3*b^2*c/9 + a^3*b*c^2/9 + 2*a^3*c^3/3 + 4*a^2*b^4/9 + a^2*b^3*c/9 - 8*a^2*b^2*c^2/3 - 8*a^2*b*c^3/9 + 4*a^2*c^4/9 + a*b^5/9 - a*b^4*c/9 - 8*a*b^3*c^2/9 + a*b^2*c^3/9 - a*b*c^4/9 + a*c^5/9 + b^5*c/9 + 4*b^4*c^2/9 + 2*b^3*c^3/3 + 4*b^2*c^4/9 + b*c^5/9) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-a^4*b*c - 3*a^3*b^2*c - 2*a^3*b*c^2 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 3*a^2*b*c^3 + 3*a^2*b + 3*a^2*c - a*b^4*c - 3*a*b^3*c^2 - 2*a*b^2*c^3 + 3*a*b^2 - a*b*c^4 + 6*a*b*c + 3*a*c^2 + 3*b^2*c + 3*b*c^2) = (a^5*b/9 + a^5*c/9 + 4*a^4*b^2/9 - a^4*b*c/9 + 4*a^4*c^2/9 + 2*a^3*b^3/3 - 8*a^3*b^2*c/9 + a^3*b*c^2/9 + 2*a^3*c^3/3 + 4*a^2*b^4/9 + a^2*b^3*c/9 - 8*a^2*b^2*c^2/3 - 8*a^2*b*c^3/9 + 4*a^2*c^4/9 + a*b^5/9 - a*b^4*c/9 - 8*a*b^3*c^2/9 + a*b^2*c^3/9 - a*b*c^4/9 + a*c^5/9 + b^5*c/9 + 4*b^4*c^2/9 + 2*b^3*c^3/3 + 4*b^2*c^4/9 + b*c^5/9) := by
    linear_combination (-a^4*b/9 - a^4*c/9 - a^3*b^2/3 - 2*a^3*b*c/3 - a^3*b/3 - a^3*c^2/3 - a^3*c/3 - a^2*b^3/3 - 10*a^2*b^2*c/9 - 2*a^2*b^2/3 - 10*a^2*b*c^2/9 - 4*a^2*b*c/3 - a^2*b - a^2*c^3/3 - 2*a^2*c^2/3 - a^2*c - a*b^4/9 - 2*a*b^3*c/3 - a*b^3/3 - 10*a*b^2*c^2/9 - 4*a*b^2*c/3 - a*b^2 - 2*a*b*c^3/3 - 4*a*b*c^2/3 - 2*a*b*c - a*c^4/9 - a*c^3/3 - a*c^2 - b^4*c/9 - b^3*c^2/3 - b^3*c/3 - b^2*c^3/3 - 2*b^2*c^2/3 - b^2*c - b*c^4/9 - b*c^3/3 - b*c^2) * habc
  have hn : 0 ≤ (-a^4*b*c - 3*a^3*b^2*c - 2*a^3*b*c^2 - 2*a^2*b^3*c - 6*a^2*b^2*c^2 - 3*a^2*b*c^3 + 3*a^2*b + 3*a^2*c - a*b^4*c - 3*a*b^3*c^2 - 2*a*b^2*c^3 + 3*a*b^2 - a*b*c^4 + 6*a*b*c + 3*a*c^2 + 3*b^2*c + 3*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) ≤ 3 / (a * b * c)) := @solution
#print axioms solution
