-- Prove2me | solution 1 for WorkbookSource.base_55115
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:25:02.742402+00:00
-- url     : https://prove2.me/submissions/9fcb0e41-9d4a-4ba7-9457-a0a321717460

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^3 + 5) / (b + 2) + (b^3 + 5) / (c + 2) + (c^3 + 5) / (a + 2) ≥ 6  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (10*a^5/9 + 35*a^4*b/27 + 80*a^4*c/27 - a^3*b^2/3 - 25*a^3*b*c/27 + a^3*c^2/3 + a^2*b^3/3 - 40*a^2*b^2*c/9 - 40*a^2*b*c^2/9 - a^2*c^3/3 + 80*a*b^4/27 - 25*a*b^3*c/27 - 40*a*b^2*c^2/9 - 25*a*b*c^3/27 + 35*a*c^4/27 + 10*b^5/9 + 35*b^4*c/27 - b^3*c^2/3 + b^2*c^3/3 + 80*b*c^4/27 + 10*c^5/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (25 : ℝ) * a^3 * (b - a)^2 + (25 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (25 : ℝ) * a^3 * (c - b)^2 + (430/9 : ℝ) * a^2 * (b - a)^3 + (233/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (253/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (245/9 : ℝ) * a^2 * (c - b)^3 + (820/27 : ℝ) * a^1 * (b - a)^4 + (1856/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (803/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (1373/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (265/27 : ℝ) * a^1 * (c - b)^4 + (175/27 : ℝ) * (b - a)^5 + (514/27 : ℝ) * (b - a)^4 * (c - b)^1 + (266/9 : ℝ) * (b - a)^3 * (c - b)^2 + (629/27 : ℝ) * (b - a)^2 * (c - b)^3 + (230/27 : ℝ) * (b - a)^1 * (c - b)^4 + (10/9 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (10*a^5/9 + 35*a^4*b/27 + 80*a^4*c/27 - a^3*b^2/3 - 25*a^3*b*c/27 + a^3*c^2/3 + a^2*b^3/3 - 40*a^2*b^2*c/9 - 40*a^2*b*c^2/9 - a^2*c^3/3 + 80*a*b^4/27 - 25*a*b^3*c/27 - 40*a*b^2*c^2/9 - 25*a*b*c^3/27 + 35*a*c^4/27 + 10*b^5/9 + 35*b^4*c/27 - b^3*c^2/3 + b^2*c^3/3 + 80*b*c^4/27 + 10*c^5/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (25 : ℝ) * a^3 * (c - a)^2 + (25 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (25 : ℝ) * a^3 * (b - c)^2 + (430/9 : ℝ) * a^2 * (c - a)^3 + (197/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (217/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (245/9 : ℝ) * a^2 * (b - c)^3 + (820/27 : ℝ) * a^1 * (c - a)^4 + (1424/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (587/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (1157/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (265/27 : ℝ) * a^1 * (b - c)^4 + (175/27 : ℝ) * (c - a)^5 + (361/27 : ℝ) * (c - a)^4 * (b - c)^1 + (164/9 : ℝ) * (c - a)^3 * (b - c)^2 + (431/27 : ℝ) * (c - a)^2 * (b - c)^3 + (185/27 : ℝ) * (c - a)^1 * (b - c)^4 + (10/9 : ℝ) * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (10*a^5/9 + 35*a^4*b/27 + 80*a^4*c/27 - a^3*b^2/3 - 25*a^3*b*c/27 + a^3*c^2/3 + a^2*b^3/3 - 40*a^2*b^2*c/9 - 40*a^2*b*c^2/9 - a^2*c^3/3 + 80*a*b^4/27 - 25*a*b^3*c/27 - 40*a*b^2*c^2/9 - 25*a*b*c^3/27 + 35*a*c^4/27 + 10*b^5/9 + 35*b^4*c/27 - b^3*c^2/3 + b^2*c^3/3 + 80*b*c^4/27 + 10*c^5/9) := by
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
  have he : (a^4*c + 2*a^4 + 2*a^3*c + 4*a^3 + a*b^4 + 2*a*b^3 - 6*a*b*c - 7*a*b - 7*a*c - 4*a + 2*b^4 + 4*b^3 + b*c^4 + 2*b*c^3 - 7*b*c - 4*b + 2*c^4 + 4*c^3 - 4*c + 12) = (10*a^5/9 + 35*a^4*b/27 + 80*a^4*c/27 - a^3*b^2/3 - 25*a^3*b*c/27 + a^3*c^2/3 + a^2*b^3/3 - 40*a^2*b^2*c/9 - 40*a^2*b*c^2/9 - a^2*c^3/3 + 80*a*b^4/27 - 25*a*b^3*c/27 - 40*a*b^2*c^2/9 - 25*a*b*c^3/27 + 35*a*c^4/27 + 10*b^5/9 + 35*b^4*c/27 - b^3*c^2/3 + b^2*c^3/3 + 80*b*c^4/27 + 10*c^5/9) := by
    linear_combination (-10*a^4/9 - 5*a^3*b/27 - 23*a^3*c/27 - 4*a^3/3 + 14*a^2*b^2/27 + 53*a^2*b*c/27 + 7*a^2*b/9 + 14*a^2*c^2/27 + 7*a^2*c/9 - 23*a*b^3/27 + 53*a*b^2*c/27 + 7*a*b^2/9 + 53*a*b*c^2/27 + 13*a*b*c/3 + 7*a*b/3 - 5*a*c^3/27 + 7*a*c^2/9 + 7*a*c/3 - 10*b^4/9 - 5*b^3*c/27 - 4*b^3/3 + 14*b^2*c^2/27 + 7*b^2*c/9 - 23*b*c^3/27 + 7*b*c^2/9 + 7*b*c/3 - 10*c^4/9 - 4*c^3/3 - 4) * habc
  have hn : 0 ≤ (a^4*c + 2*a^4 + 2*a^3*c + 4*a^3 + a*b^4 + 2*a*b^3 - 6*a*b*c - 7*a*b - 7*a*c - 4*a + 2*b^4 + 4*b^3 + b*c^4 + 2*b*c^3 - 7*b*c - 4*b + 2*c^4 + 4*c^3 - 4*c + 12) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^3 + 5) / (b + 2) + (b^3 + 5) / (c + 2) + (c^3 + 5) / (a + 2) ≥ 6) := @solution
#print axioms solution
