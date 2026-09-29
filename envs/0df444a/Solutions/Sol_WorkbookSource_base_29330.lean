-- Prove2me | solution 1 for WorkbookSource.base_29330
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:14:17.091778+00:00
-- url     : https://prove2.me/submissions/4e7e2458-d9b7-49cd-a90d-add06b007482

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a) + 3 / (a + b + c) ≥ 4 * (1 / (3 * a + 2 * b + c) + 1 / (a + 3 * b + 2 * c) + 1 / (2 * a + b + 3 * c))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (12*a^6 + 52*a^5*b - 4*a^5*c + 83*a^4*b^2 + 6*a^4*b*c - 41*a^4*c^2 + 30*a^3*b^3 - 20*a^3*b^2*c - 88*a^3*b*c^2 + 30*a^3*c^3 - 41*a^2*b^4 - 88*a^2*b^3*c - 90*a^2*b^2*c^2 - 20*a^2*b*c^3 + 83*a^2*c^4 - 4*a*b^5 + 6*a*b^4*c - 20*a*b^3*c^2 - 88*a*b^2*c^3 + 6*a*b*c^4 + 52*a*c^5 + 12*b^6 + 52*b^5*c + 83*b^4*c^2 + 30*b^3*c^3 - 41*b^2*c^4 - 4*b*c^5 + 12*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (648 : ℝ) * a^4 * (b - a)^2 + (648 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (648 : ℝ) * a^4 * (c - b)^2 + (1728 : ℝ) * a^3 * (b - a)^3 + (1782 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1782 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (864 : ℝ) * a^3 * (c - b)^3 + (1764 : ℝ) * a^2 * (b - a)^4 + (1908 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1566 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1422 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (468 : ℝ) * a^2 * (c - b)^4 + (816 : ℝ) * a^1 * (b - a)^5 + (966 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (540 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (654 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (504 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (120 : ℝ) * a^1 * (c - b)^5 + (144 : ℝ) * (b - a)^6 + (196 : ℝ) * (b - a)^5 * (c - b)^1 + (67 : ℝ) * (b - a)^4 * (c - b)^2 + (66 : ℝ) * (b - a)^3 * (c - b)^3 + (119 : ℝ) * (b - a)^2 * (c - b)^4 + (68 : ℝ) * (b - a)^1 * (c - b)^5 + (12 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (12*a^6 + 52*a^5*b - 4*a^5*c + 83*a^4*b^2 + 6*a^4*b*c - 41*a^4*c^2 + 30*a^3*b^3 - 20*a^3*b^2*c - 88*a^3*b*c^2 + 30*a^3*c^3 - 41*a^2*b^4 - 88*a^2*b^3*c - 90*a^2*b^2*c^2 - 20*a^2*b*c^3 + 83*a^2*c^4 - 4*a*b^5 + 6*a*b^4*c - 20*a*b^3*c^2 - 88*a*b^2*c^3 + 6*a*b*c^4 + 52*a*c^5 + 12*b^6 + 52*b^5*c + 83*b^4*c^2 + 30*b^3*c^3 - 41*b^2*c^4 - 4*b*c^5 + 12*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (648 : ℝ) * a^4 * (c - a)^2 + (648 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (648 : ℝ) * a^4 * (b - c)^2 + (1728 : ℝ) * a^3 * (c - a)^3 + (3402 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (3402 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (864 : ℝ) * a^3 * (b - c)^3 + (1764 : ℝ) * a^2 * (c - a)^4 + (5148 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (6426 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (3042 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (468 : ℝ) * a^2 * (b - c)^4 + (816 : ℝ) * a^1 * (c - a)^5 + (3114 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (4836 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (3330 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1032 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (120 : ℝ) * a^1 * (b - c)^5 + (144 : ℝ) * (c - a)^6 + (668 : ℝ) * (c - a)^5 * (b - c)^1 + (1247 : ℝ) * (c - a)^4 * (b - c)^2 + (1122 : ℝ) * (c - a)^3 * (b - c)^3 + (523 : ℝ) * (c - a)^2 * (b - c)^4 + (124 : ℝ) * (c - a)^1 * (b - c)^5 + (12 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*a^6 + 52*a^5*b - 4*a^5*c + 83*a^4*b^2 + 6*a^4*b*c - 41*a^4*c^2 + 30*a^3*b^3 - 20*a^3*b^2*c - 88*a^3*b*c^2 + 30*a^3*c^3 - 41*a^2*b^4 - 88*a^2*b^3*c - 90*a^2*b^2*c^2 - 20*a^2*b*c^3 + 83*a^2*c^4 - 4*a*b^5 + 6*a*b^4*c - 20*a*b^3*c^2 - 88*a*b^2*c^3 + 6*a*b*c^4 + 52*a*c^5 + 12*b^6 + 52*b^5*c + 83*b^4*c^2 + 30*b^3*c^3 - 41*b^2*c^4 - 4*b*c^5 + 12*c^6) := by
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
  have hn : 0 ≤ (12*a^6 + 52*a^5*b - 4*a^5*c + 83*a^4*b^2 + 6*a^4*b*c - 41*a^4*c^2 + 30*a^3*b^3 - 20*a^3*b^2*c - 88*a^3*b*c^2 + 30*a^3*c^3 - 41*a^2*b^4 - 88*a^2*b^3*c - 90*a^2*b^2*c^2 - 20*a^2*b*c^3 + 83*a^2*c^4 - 4*a*b^5 + 6*a*b^4*c - 20*a*b^3*c^2 - 88*a*b^2*c^3 + 6*a*b*c^4 + 52*a*c^5 + 12*b^6 + 52*b^5*c + 83*b^4*c^2 + 30*b^3*c^3 - 41*b^2*c^4 - 4*b*c^5 + 12*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a) + 3 / (a + b + c) ≥ 4 * (1 / (3 * a + 2 * b + c) + 1 / (a + 3 * b + 2 * c) + 1 / (2 * a + b + 3 * c))) := @solution
#print axioms solution
