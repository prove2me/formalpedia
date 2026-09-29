-- Prove2me | solution 1 for WorkbookSource.base_34270
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:07.587603+00:00
-- url     : https://prove2.me/submissions/84830aa7-d1a2-44af-ba40-6062d58e520e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (a ^ 2 + b * c + 1) + b / (b ^ 2 + c * a + 1) + c / (c ^ 2 + a * b + 1) ≤ 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (7*a^6/729 + 20*a^5*b/243 + 20*a^5*c/243 - 49*a^4*b^2/243 + 232*a^4*b*c/243 - 49*a^4*c^2/243 + 329*a^3*b^3/729 - 187*a^3*b^2*c/243 - 187*a^3*b*c^2/243 + 329*a^3*c^3/729 - 49*a^2*b^4/243 - 187*a^2*b^3*c/243 + 88*a^2*b^2*c^2/81 - 187*a^2*b*c^3/243 - 49*a^2*c^4/243 + 20*a*b^5/243 + 232*a*b^4*c/243 - 187*a*b^3*c^2/243 - 187*a*b^2*c^3/243 + 232*a*b*c^4/243 + 20*a*c^5/243 + 7*b^6/729 + 20*b^5*c/243 - 49*b^4*c^2/243 + 329*b^3*c^3/729 - 49*b^2*c^4/243 + 20*b*c^5/243 + 7*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (7/3 : ℝ) * a^4 * (b - a)^2 + (7/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (7/3 : ℝ) * a^4 * (c - b)^2 + (160/27 : ℝ) * a^3 * (b - a)^3 + (80/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (88/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (92/27 : ℝ) * a^3 * (c - b)^3 + (143/27 : ℝ) * a^2 * (b - a)^4 + (286/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (121/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (220/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (41/27 : ℝ) * a^2 * (c - b)^4 + (52/27 : ℝ) * a^1 * (b - a)^5 + (130/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (64/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (158/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (56/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2/9 : ℝ) * a^1 * (c - b)^5 + (169/729 : ℝ) * (b - a)^6 + (169/243 : ℝ) * (b - a)^5 * (c - b)^1 + (221/243 : ℝ) * (b - a)^4 * (c - b)^2 + (481/729 : ℝ) * (b - a)^3 * (c - b)^3 + (86/243 : ℝ) * (b - a)^2 * (c - b)^4 + (34/243 : ℝ) * (b - a)^1 * (c - b)^5 + (7/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (7*a^6/729 + 20*a^5*b/243 + 20*a^5*c/243 - 49*a^4*b^2/243 + 232*a^4*b*c/243 - 49*a^4*c^2/243 + 329*a^3*b^3/729 - 187*a^3*b^2*c/243 - 187*a^3*b*c^2/243 + 329*a^3*c^3/729 - 49*a^2*b^4/243 - 187*a^2*b^3*c/243 + 88*a^2*b^2*c^2/81 - 187*a^2*b*c^3/243 - 49*a^2*c^4/243 + 20*a*b^5/243 + 232*a*b^4*c/243 - 187*a*b^3*c^2/243 - 187*a*b^2*c^3/243 + 232*a*b*c^4/243 + 20*a*c^5/243 + 7*b^6/729 + 20*b^5*c/243 - 49*b^4*c^2/243 + 329*b^3*c^3/729 - 49*b^2*c^4/243 + 20*b*c^5/243 + 7*c^6/729) := by
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
  have he : (a^4*b*c + a^3*b^3 - a^3*b^2 - a^3*b*c + a^3*b + a^3*c^3 - a^3*c^2 + a^3*c - a^2*b^3 + 2*a^2*b^2*c^2 - a^2*b^2*c + a^2*b^2 - a^2*b*c^2 + a^2*b*c - 2*a^2*b - a^2*c^3 + a^2*c^2 - 2*a^2*c + a^2 + a*b^4*c - a*b^3*c + a*b^3 - a*b^2*c^2 + a*b^2*c - 2*a*b^2 + a*b*c^4 - a*b*c^3 + a*b*c^2 + a*b + a*c^3 - 2*a*c^2 + a*c - a + b^3*c^3 - b^3*c^2 + b^3*c - b^2*c^3 + b^2*c^2 - 2*b^2*c + b^2 + b*c^3 - 2*b*c^2 + b*c - b + c^2 - c + 1) = (7*a^6/729 + 20*a^5*b/243 + 20*a^5*c/243 - 49*a^4*b^2/243 + 232*a^4*b*c/243 - 49*a^4*c^2/243 + 329*a^3*b^3/729 - 187*a^3*b^2*c/243 - 187*a^3*b*c^2/243 + 329*a^3*c^3/729 - 49*a^2*b^4/243 - 187*a^2*b^3*c/243 + 88*a^2*b^2*c^2/81 - 187*a^2*b*c^3/243 - 49*a^2*c^4/243 + 20*a*b^5/243 + 232*a*b^4*c/243 - 187*a*b^3*c^2/243 - 187*a*b^2*c^3/243 + 232*a*b*c^4/243 + 20*a*c^5/243 + 7*b^6/729 + 20*b^5*c/243 - 49*b^4*c^2/243 + 329*b^3*c^3/729 - 49*b^2*c^4/243 + 20*b*c^5/243 + 7*c^6/729) := by
    linear_combination (-7*a^5/729 - 53*a^4*b/729 - 53*a^4*c/729 - 7*a^4/243 + 200*a^3*b^2/729 + 139*a^3*b*c/729 - 46*a^3*b/243 + 200*a^3*c^2/729 - 46*a^3*c/243 - 7*a^3/81 + 200*a^2*b^3/729 + 74*a^2*b^2*c/243 + a^2*b^2/81 + 74*a^2*b*c^2/243 - 4*a^2*b*c/81 + 14*a^2*b/27 + 200*a^2*c^3/729 + a^2*c^2/81 + 14*a^2*c/27 - 7*a^2/27 - 53*a*b^4/729 + 139*a*b^3*c/729 - 46*a*b^3/243 + 74*a*b^2*c^2/243 - 4*a*b^2*c/81 + 14*a*b^2/27 + 139*a*b*c^3/729 - 4*a*b*c^2/81 - 5*a*b*c/27 - 5*a*b/27 - 53*a*c^4/729 - 46*a*c^3/243 + 14*a*c^2/27 - 5*a*c/27 + 2*a/9 - 7*b^5/729 - 53*b^4*c/729 - 7*b^4/243 + 200*b^3*c^2/729 - 46*b^3*c/243 - 7*b^3/81 + 200*b^2*c^3/729 + b^2*c^2/81 + 14*b^2*c/27 - 7*b^2/27 - 53*b*c^4/729 - 46*b*c^3/243 + 14*b*c^2/27 - 5*b*c/27 + 2*b/9 - 7*c^5/729 - 7*c^4/243 - 7*c^3/81 - 7*c^2/27 + 2*c/9 - 1/3) * hab
  have hn : 0 ≤ (a^4*b*c + a^3*b^3 - a^3*b^2 - a^3*b*c + a^3*b + a^3*c^3 - a^3*c^2 + a^3*c - a^2*b^3 + 2*a^2*b^2*c^2 - a^2*b^2*c + a^2*b^2 - a^2*b*c^2 + a^2*b*c - 2*a^2*b - a^2*c^3 + a^2*c^2 - 2*a^2*c + a^2 + a*b^4*c - a*b^3*c + a*b^3 - a*b^2*c^2 + a*b^2*c - 2*a*b^2 + a*b*c^4 - a*b*c^3 + a*b*c^2 + a*b + a*c^3 - 2*a*c^2 + a*c - a + b^3*c^3 - b^3*c^2 + b^3*c - b^2*c^3 + b^2*c^2 - 2*b^2*c + b^2 + b*c^3 - 2*b*c^2 + b*c - b + c^2 - c + 1) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a / (a ^ 2 + b * c + 1) + b / (b ^ 2 + c * a + 1) + c / (c ^ 2 + a * b + 1) ≤ 1) := @solution
#print axioms solution
