-- Prove2me | solution 1 for WorkbookSource.base_33663
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:38:40.770519+00:00
-- url     : https://prove2.me/submissions/acd21d0b-d543-46aa-b1e6-a521d523ef27

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (4 * a + 5 * b * c) + b / (4 * b + 5 * c * a) + c / (4 * c + 5 * a * b) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 9  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (40*a^6*b^2/9 + 691*a^6*b*c/27 + 40*a^6*c^2/9 + 59*a^5*b^2*c/9 + 59*a^5*b*c^2/9 - 80*a^4*b^4/9 - 284*a^4*b^3*c/27 + 121*a^4*b^2*c^2/3 - 284*a^4*b*c^3/27 - 80*a^4*c^4/9 - 284*a^3*b^4*c/27 - 58*a^3*b^3*c^2 - 58*a^3*b^2*c^3 - 284*a^3*b*c^4/27 + 40*a^2*b^6/9 + 59*a^2*b^5*c/9 + 121*a^2*b^4*c^2/3 - 58*a^2*b^3*c^3 + 121*a^2*b^2*c^4/3 + 59*a^2*b*c^5/9 + 40*a^2*c^6/9 + 691*a*b^6*c/27 + 59*a*b^5*c^2/9 - 284*a*b^4*c^3/27 - 284*a*b^3*c^4/27 + 59*a*b^2*c^5/9 + 691*a*b*c^6/27 + 40*b^6*c^2/9 - 80*b^4*c^4/9 + 40*b^2*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (291 : ℝ) * a^6 * (b - a)^2 + (291 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (291 : ℝ) * a^6 * (c - b)^2 + (9506/9 : ℝ) * a^5 * (b - a)^3 + (4753/3 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (5723/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (6208/9 : ℝ) * a^5 * (c - b)^3 + (40511/27 : ℝ) * a^4 * (b - a)^4 + (81022/27 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (39541/9 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (78112/27 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (15776/27 : ℝ) * a^4 * (c - b)^4 + (28064/27 : ℝ) * a^3 * (b - a)^5 + (70160/27 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (4636 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (117598/27 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (46402/27 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (220 : ℝ) * a^3 * (c - b)^5 + (9382/27 : ℝ) * a^2 * (b - a)^6 + (9382/9 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (20825/9 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (78040/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (15344/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (3901/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (931/27 : ℝ) * a^2 * (c - b)^6 + (1168/27 : ℝ) * a^1 * (b - a)^7 + (4088/27 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (468 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (21370/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (17206/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (2161/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (931/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (160/9 : ℝ) * (b - a)^6 * (c - b)^2 + (160/3 : ℝ) * (b - a)^5 * (c - b)^3 + (520/9 : ℝ) * (b - a)^4 * (c - b)^4 + (80/3 : ℝ) * (b - a)^3 * (c - b)^5 + (40/9 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (40*a^6*b^2/9 + 691*a^6*b*c/27 + 40*a^6*c^2/9 + 59*a^5*b^2*c/9 + 59*a^5*b*c^2/9 - 80*a^4*b^4/9 - 284*a^4*b^3*c/27 + 121*a^4*b^2*c^2/3 - 284*a^4*b*c^3/27 - 80*a^4*c^4/9 - 284*a^3*b^4*c/27 - 58*a^3*b^3*c^2 - 58*a^3*b^2*c^3 - 284*a^3*b*c^4/27 + 40*a^2*b^6/9 + 59*a^2*b^5*c/9 + 121*a^2*b^4*c^2/3 - 58*a^2*b^3*c^3 + 121*a^2*b^2*c^4/3 + 59*a^2*b*c^5/9 + 40*a^2*c^6/9 + 691*a*b^6*c/27 + 59*a*b^5*c^2/9 - 284*a*b^4*c^3/27 - 284*a*b^3*c^4/27 + 59*a*b^2*c^5/9 + 691*a*b*c^6/27 + 40*b^6*c^2/9 - 80*b^4*c^4/9 + 40*b^2*c^6/9) := by
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
  have he : (100*a^5*b*c + 125*a^4*b^2*c^2 + 80*a^4*b^2 + 80*a^4*c^2 + 200*a^3*b^3*c + 200*a^3*b*c^3 - 161*a^3*b*c + 125*a^2*b^4*c^2 + 80*a^2*b^4 + 125*a^2*b^2*c^4 + 240*a^2*b^2*c^2 - 360*a^2*b^2 + 80*a^2*c^4 - 360*a^2*c^2 + 100*a*b^5*c + 200*a*b^3*c^3 - 161*a*b^3*c + 100*a*b*c^5 - 161*a*b*c^3 - 432*a*b*c + 80*b^4*c^2 + 80*b^2*c^4 - 360*b^2*c^2) = (40*a^6*b^2/9 + 691*a^6*b*c/27 + 40*a^6*c^2/9 + 59*a^5*b^2*c/9 + 59*a^5*b*c^2/9 - 80*a^4*b^4/9 - 284*a^4*b^3*c/27 + 121*a^4*b^2*c^2/3 - 284*a^4*b*c^3/27 - 80*a^4*c^4/9 - 284*a^3*b^4*c/27 - 58*a^3*b^3*c^2 - 58*a^3*b^2*c^3 - 284*a^3*b*c^4/27 + 40*a^2*b^6/9 + 59*a^2*b^5*c/9 + 121*a^2*b^4*c^2/3 - 58*a^2*b^3*c^3 + 121*a^2*b^2*c^4/3 + 59*a^2*b*c^5/9 + 40*a^2*c^6/9 + 691*a*b^6*c/27 + 59*a*b^5*c^2/9 - 284*a*b^4*c^3/27 - 284*a*b^3*c^4/27 + 59*a*b^2*c^5/9 + 691*a*b*c^6/27 + 40*b^6*c^2/9 - 80*b^4*c^4/9 + 40*b^2*c^6/9) := by
    linear_combination (-40*a^5*b^2/9 - 691*a^5*b*c/27 - 40*a^5*c^2/9 + 40*a^4*b^3/9 + 634*a^4*b^2*c/27 - 40*a^4*b^2/3 + 634*a^4*b*c^2/27 + 209*a^4*b*c/9 + 40*a^4*c^3/9 - 40*a^4*c^2/3 + 40*a^3*b^4/9 - 470*a^3*b^3*c/27 + 80*a^3*b^3/3 + 1018*a^3*b^2*c^2/27 + 545*a^3*b^2*c/9 + 40*a^3*b^2 - 470*a^3*b*c^3/27 + 545*a^3*b*c^2/9 + 209*a^3*b*c/3 + 40*a^3*c^4/9 + 80*a^3*c^3/3 + 40*a^3*c^2 - 40*a^2*b^5/9 + 634*a^2*b^4*c/27 - 40*a^2*b^4/3 + 1018*a^2*b^3*c^2/27 + 545*a^2*b^3*c/9 + 40*a^2*b^3 + 1018*a^2*b^2*c^3/27 - 8*a^2*b^2*c^2 + 72*a^2*b^2*c + 120*a^2*b^2 + 634*a^2*b*c^4/27 + 545*a^2*b*c^3/9 + 72*a^2*b*c^2 + 48*a^2*b*c - 40*a^2*c^5/9 - 40*a^2*c^4/3 + 40*a^2*c^3 + 120*a^2*c^2 - 691*a*b^5*c/27 + 634*a*b^4*c^2/27 + 209*a*b^4*c/9 - 470*a*b^3*c^3/27 + 545*a*b^3*c^2/9 + 209*a*b^3*c/3 + 634*a*b^2*c^4/27 + 545*a*b^2*c^3/9 + 72*a*b^2*c^2 + 48*a*b^2*c - 691*a*b*c^5/27 + 209*a*b*c^4/9 + 209*a*b*c^3/3 + 48*a*b*c^2 + 144*a*b*c - 40*b^5*c^2/9 + 40*b^4*c^3/9 - 40*b^4*c^2/3 + 40*b^3*c^4/9 + 80*b^3*c^3/3 + 40*b^3*c^2 - 40*b^2*c^5/9 - 40*b^2*c^4/3 + 40*b^2*c^3 + 120*b^2*c^2) * habc
  have hn : 0 ≤ (100*a^5*b*c + 125*a^4*b^2*c^2 + 80*a^4*b^2 + 80*a^4*c^2 + 200*a^3*b^3*c + 200*a^3*b*c^3 - 161*a^3*b*c + 125*a^2*b^4*c^2 + 80*a^2*b^4 + 125*a^2*b^2*c^4 + 240*a^2*b^2*c^2 - 360*a^2*b^2 + 80*a^2*c^4 - 360*a^2*c^2 + 100*a*b^5*c + 200*a*b^3*c^3 - 161*a*b^3*c + 100*a*b*c^5 - 161*a*b*c^3 - 432*a*b*c + 80*b^4*c^2 + 80*b^2*c^4 - 360*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / (4 * a + 5 * b * c) + b / (4 * b + 5 * c * a) + c / (4 * c + 5 * a * b) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 9) := @solution
#print axioms solution
