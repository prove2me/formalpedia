-- Prove2me | solution 1 for WorkbookSource.base_23740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:58:37.421546+00:00
-- url     : https://prove2.me/submissions/f1f06413-1275-47b5-afe5-c6e3ee9deda3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a + b) + b / (b + c) + c / (c + a) ≤ 3 / (1 + a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b/27 + 2*a^5*c/27 + 5*a^4*b^2/27 + 4*a^4*b*c/9 + 7*a^4*c^2/27 + a^3*b^3/3 - 26*a^3*b^2*c/27 + 2*a^3*b*c^2/27 + a^3*c^3/3 + 7*a^2*b^4/27 + 2*a^2*b^3*c/27 - 4*a^2*b^2*c^2/3 - 26*a^2*b*c^3/27 + 5*a^2*c^4/27 + 2*a*b^5/27 + 4*a*b^4*c/9 - 26*a*b^3*c^2/27 + 2*a*b^2*c^3/27 + 4*a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 5*b^4*c^2/27 + b^3*c^3/3 + 7*b^2*c^4/27 + 2*b*c^5/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^4 * (b - a)^2 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^4 * (c - b)^2 + (104/9 : ℝ) * a^3 * (b - a)^3 + (55/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (47/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (40/9 : ℝ) * a^3 * (c - b)^3 + (109/9 : ℝ) * a^2 * (b - a)^4 + (236/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (74/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (95/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (13/9 : ℝ) * a^2 * (c - b)^4 + (49/9 : ℝ) * a^1 * (b - a)^5 + (133/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (146/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (77/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (17/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1/9 : ℝ) * a^1 * (c - b)^5 + (8/9 : ℝ) * (b - a)^6 + (76/27 : ℝ) * (b - a)^5 * (c - b)^1 + (94/27 : ℝ) * (b - a)^4 * (c - b)^2 + (19/9 : ℝ) * (b - a)^3 * (c - b)^3 + (17/27 : ℝ) * (b - a)^2 * (c - b)^4 + (2/27 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b/27 + 2*a^5*c/27 + 5*a^4*b^2/27 + 4*a^4*b*c/9 + 7*a^4*c^2/27 + a^3*b^3/3 - 26*a^3*b^2*c/27 + 2*a^3*b*c^2/27 + a^3*c^3/3 + 7*a^2*b^4/27 + 2*a^2*b^3*c/27 - 4*a^2*b^2*c^2/3 - 26*a^2*b*c^3/27 + 5*a^2*c^4/27 + 2*a*b^5/27 + 4*a*b^4*c/9 - 26*a*b^3*c^2/27 + 2*a*b^2*c^3/27 + 4*a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 5*b^4*c^2/27 + b^3*c^3/3 + 7*b^2*c^4/27 + 2*b*c^5/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^4 * (c - a)^2 + (4 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^4 * (b - c)^2 + (104/9 : ℝ) * a^3 * (c - a)^3 + (49/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (41/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (40/9 : ℝ) * a^3 * (b - c)^3 + (109/9 : ℝ) * a^2 * (c - a)^4 + (200/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (56/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (77/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (13/9 : ℝ) * a^2 * (b - c)^4 + (49/9 : ℝ) * a^1 * (c - a)^5 + (112/9 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (104/9 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (53/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (14/9 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (1/9 : ℝ) * a^1 * (b - c)^5 + (8/9 : ℝ) * (c - a)^6 + (68/27 : ℝ) * (c - a)^5 * (b - c)^1 + (74/27 : ℝ) * (c - a)^4 * (b - c)^2 + (13/9 : ℝ) * (c - a)^3 * (b - c)^3 + (10/27 : ℝ) * (c - a)^2 * (b - c)^4 + (1/27 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b/27 + 2*a^5*c/27 + 5*a^4*b^2/27 + 4*a^4*b*c/9 + 7*a^4*c^2/27 + a^3*b^3/3 - 26*a^3*b^2*c/27 + 2*a^3*b*c^2/27 + a^3*c^3/3 + 7*a^2*b^4/27 + 2*a^2*b^3*c/27 - 4*a^2*b^2*c^2/3 - 26*a^2*b*c^3/27 + 5*a^2*c^4/27 + 2*a*b^5/27 + 4*a*b^4*c/9 - 26*a*b^3*c^2/27 + 2*a*b^2*c^3/27 + 4*a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 5*b^4*c^2/27 + b^3*c^3/3 + 7*b^2*c^4/27 + 2*b*c^5/27) := by
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
  have he : (-2*a^3*b^2*c - a^3*b*c^2 - a^2*b^3*c - 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*b + 2*a^2*c - 2*a*b^3*c^2 - a*b^2*c^3 + 2*a*b^2 + 3*a*b*c + a*c^2 + b^2*c + 2*b*c^2) = (a^5*b/27 + 2*a^5*c/27 + 5*a^4*b^2/27 + 4*a^4*b*c/9 + 7*a^4*c^2/27 + a^3*b^3/3 - 26*a^3*b^2*c/27 + 2*a^3*b*c^2/27 + a^3*c^3/3 + 7*a^2*b^4/27 + 2*a^2*b^3*c/27 - 4*a^2*b^2*c^2/3 - 26*a^2*b*c^3/27 + 5*a^2*c^4/27 + 2*a*b^5/27 + 4*a*b^4*c/9 - 26*a*b^3*c^2/27 + 2*a*b^2*c^3/27 + 4*a*b*c^4/9 + a*c^5/27 + b^5*c/27 + 5*b^4*c^2/27 + b^3*c^3/3 + 7*b^2*c^4/27 + 2*b*c^5/27) := by
    linear_combination (-a^4*b/27 - 2*a^4*c/27 - 4*a^3*b^2/27 - a^3*b*c/3 - a^3*b/9 - 5*a^3*c^2/27 - 2*a^3*c/9 - 5*a^2*b^3/27 - 5*a^2*b^2*c/9 - a^2*b^2/3 - 5*a^2*b*c^2/9 - 2*a^2*b*c/3 - a^2*b/3 - 4*a^2*c^3/27 - a^2*c^2/3 - 2*a^2*c/3 - 2*a*b^4/27 - a*b^3*c/3 - 2*a*b^3/9 - 5*a*b^2*c^2/9 - 2*a*b^2*c/3 - 2*a*b^2/3 - a*b*c^3/3 - 2*a*b*c^2/3 - a*b*c - a*c^4/27 - a*c^3/9 - a*c^2/3 - b^4*c/27 - 4*b^3*c^2/27 - b^3*c/9 - 5*b^2*c^3/27 - b^2*c^2/3 - b^2*c/3 - 2*b*c^4/27 - 2*b*c^3/9 - 2*b*c^2/3) * hab
  have hn : 0 ≤ (-2*a^3*b^2*c - a^3*b*c^2 - a^2*b^3*c - 3*a^2*b^2*c^2 - 2*a^2*b*c^3 + a^2*b + 2*a^2*c - 2*a*b^3*c^2 - a*b^2*c^3 + 2*a*b^2 + 3*a*b*c + a*c^2 + b^2*c + 2*b*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (a + b) + b / (b + c) + c / (c + a) ≤ 3 / (1 + a * b * c)) := @solution
#print axioms solution
