-- Prove2me | solution 1 for WorkbookSource.plus_58086
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:51:26.886666+00:00
-- url     : https://prove2.me/submissions/5a5dd2c6-a5c1-41da-8edf-a5948b65e4d5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : 1 ≤ 1 / (2 * a ^ 2 + 1) + 1 / (2 * b ^ 2 + 1) + 1 / (2 * c ^ 2 + 1)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (20*a^6/729 + 28*a^5*b/243 + 28*a^5*c/243 + 52*a^4*b^2/243 + 92*a^4*b*c/243 + 52*a^4*c^2/243 + 184*a^3*b^3/729 + 136*a^3*b^2*c/243 + 136*a^3*b*c^2/243 + 184*a^3*c^3/729 + 52*a^2*b^4/243 + 136*a^2*b^3*c/243 - 592*a^2*b^2*c^2/81 + 136*a^2*b*c^3/243 + 52*a^2*c^4/243 + 28*a*b^5/243 + 92*a*b^4*c/243 + 136*a*b^3*c^2/243 + 136*a*b^2*c^3/243 + 92*a*b*c^4/243 + 28*a*c^5/243 + 20*b^6/729 + 28*b^5*c/243 + 52*b^4*c^2/243 + 184*b^3*c^3/729 + 52*b^2*c^4/243 + 28*b*c^5/243 + 20*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20/3 : ℝ) * a^4 * (b - a)^2 + (20/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (20/3 : ℝ) * a^4 * (c - b)^2 + (512/27 : ℝ) * a^3 * (b - a)^3 + (256/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (224/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (208/27 : ℝ) * a^3 * (c - b)^3 + (520/27 : ℝ) * a^2 * (b - a)^4 + (1040/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (320/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (440/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (64/27 : ℝ) * a^2 * (c - b)^4 + (640/81 : ℝ) * a^1 * (b - a)^5 + (1600/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1696/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (944/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (272/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (32/81 : ℝ) * a^1 * (c - b)^5 + (704/729 : ℝ) * (b - a)^6 + (704/243 : ℝ) * (b - a)^5 * (c - b)^1 + (928/243 : ℝ) * (b - a)^4 * (c - b)^2 + (2048/729 : ℝ) * (b - a)^3 * (c - b)^3 + (292/243 : ℝ) * (b - a)^2 * (c - b)^4 + (68/243 : ℝ) * (b - a)^1 * (c - b)^5 + (20/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (20*a^6/729 + 28*a^5*b/243 + 28*a^5*c/243 + 52*a^4*b^2/243 + 92*a^4*b*c/243 + 52*a^4*c^2/243 + 184*a^3*b^3/729 + 136*a^3*b^2*c/243 + 136*a^3*b*c^2/243 + 184*a^3*c^3/729 + 52*a^2*b^4/243 + 136*a^2*b^3*c/243 - 592*a^2*b^2*c^2/81 + 136*a^2*b*c^3/243 + 52*a^2*c^4/243 + 28*a*b^5/243 + 92*a*b^4*c/243 + 136*a*b^3*c^2/243 + 136*a*b^2*c^3/243 + 92*a*b*c^4/243 + 28*a*c^5/243 + 20*b^6/729 + 28*b^5*c/243 + 52*b^4*c^2/243 + 184*b^3*c^3/729 + 52*b^2*c^4/243 + 28*b*c^5/243 + 20*c^6/729) := by
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
  have he : (-8*a^2*b^2*c^2 + 2*a^2 + 2*b^2 + 2*c^2 + 2) = (20*a^6/729 + 28*a^5*b/243 + 28*a^5*c/243 + 52*a^4*b^2/243 + 92*a^4*b*c/243 + 52*a^4*c^2/243 + 184*a^3*b^3/729 + 136*a^3*b^2*c/243 + 136*a^3*b*c^2/243 + 184*a^3*c^3/729 + 52*a^2*b^4/243 + 136*a^2*b^3*c/243 - 592*a^2*b^2*c^2/81 + 136*a^2*b*c^3/243 + 52*a^2*c^4/243 + 28*a*b^5/243 + 92*a*b^4*c/243 + 136*a*b^3*c^2/243 + 136*a*b^2*c^3/243 + 92*a*b*c^4/243 + 28*a*c^5/243 + 20*b^6/729 + 28*b^5*c/243 + 52*b^4*c^2/243 + 184*b^3*c^3/729 + 52*b^2*c^4/243 + 28*b*c^5/243 + 20*c^6/729) := by
    linear_combination (-20*a^5/729 - 64*a^4*b/729 - 64*a^4*c/729 - 20*a^4/243 - 92*a^3*b^2/729 - 148*a^3*b*c/729 - 44*a^3*b/243 - 92*a^3*c^2/729 - 44*a^3*c/243 - 20*a^3/81 - 92*a^2*b^3/729 - 56*a^2*b^2*c/243 - 16*a^2*b^2/81 - 56*a^2*b*c^2/243 - 20*a^2*b*c/81 - 8*a^2*b/27 - 92*a^2*c^3/729 - 16*a^2*c^2/81 - 8*a^2*c/27 - 20*a^2/27 - 64*a*b^4/729 - 148*a*b^3*c/729 - 44*a*b^3/243 - 56*a*b^2*c^2/243 - 20*a*b^2*c/81 - 8*a*b^2/27 - 148*a*b*c^3/729 - 20*a*b*c^2/81 - 4*a*b*c/27 - 4*a*b/27 - 64*a*c^4/729 - 44*a*c^3/243 - 8*a*c^2/27 - 4*a*c/27 - 2*a/9 - 20*b^5/729 - 64*b^4*c/729 - 20*b^4/243 - 92*b^3*c^2/729 - 44*b^3*c/243 - 20*b^3/81 - 92*b^2*c^3/729 - 16*b^2*c^2/81 - 8*b^2*c/27 - 20*b^2/27 - 64*b*c^4/729 - 44*b*c^3/243 - 8*b*c^2/27 - 4*b*c/27 - 2*b/9 - 20*c^5/729 - 20*c^4/243 - 20*c^3/81 - 20*c^2/27 - 2*c/9 - 2/3) * habc
  have hn : 0 ≤ (-8*a^2*b^2*c^2 + 2*a^2 + 2*b^2 + 2*c^2 + 2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3), 1 ≤ 1 / (2 * a ^ 2 + 1) + 1 / (2 * b ^ 2 + 1) + 1 / (2 * c ^ 2 + 1)) := @solution
#print axioms solution
