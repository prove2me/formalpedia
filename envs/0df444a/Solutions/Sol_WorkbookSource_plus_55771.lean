-- Prove2me | solution 1 for WorkbookSource.plus_55771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:42:11.782466+00:00
-- url     : https://prove2.me/submissions/a984979a-b320-4699-84fa-fd2adabc81b1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (b ^ 2 + 2) + b / (c ^ 2 + 2) + c / (a ^ 2 + 2) ≥ 1   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (22*a^6/729 + 32*a^5*b/243 + 14*a^5*c/243 - 10*a^4*b^2/243 + 58*a^4*b*c/243 + 35*a^4*c^2/243 - 19*a^3*b^3/729 - 40*a^3*b^2*c/243 + 23*a^3*b*c^2/243 - 19*a^3*c^3/729 + 35*a^2*b^4/243 + 23*a^2*b^3*c/243 - 113*a^2*b^2*c^2/81 - 40*a^2*b*c^3/243 - 10*a^2*c^4/243 + 14*a*b^5/243 + 58*a*b^4*c/243 - 40*a*b^3*c^2/243 + 23*a*b^2*c^3/243 + 58*a*b*c^4/243 + 32*a*c^5/243 + 22*b^6/729 + 32*b^5*c/243 - 10*b^4*c^2/243 - 19*b^3*c^3/729 + 35*b^2*c^4/243 + 14*b*c^5/243 + 22*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8/3 : ℝ) * a^4 * (b - a)^2 + (8/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8/3 : ℝ) * a^4 * (c - b)^2 + (187/27 : ℝ) * a^3 * (b - a)^3 + (98/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (103/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (101/27 : ℝ) * a^3 * (c - b)^3 + (176/27 : ℝ) * a^2 * (b - a)^4 + (379/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (154/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (259/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (47/27 : ℝ) * a^2 * (c - b)^4 + (23/9 : ℝ) * a^1 * (b - a)^5 + (62/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (269/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (68/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (8/3 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10/27 : ℝ) * a^1 * (c - b)^5 + (238/729 : ℝ) * (b - a)^6 + (247/243 : ℝ) * (b - a)^5 * (c - b)^1 + (431/243 : ℝ) * (b - a)^4 * (c - b)^2 + (1261/729 : ℝ) * (b - a)^3 * (c - b)^3 + (215/243 : ℝ) * (b - a)^2 * (c - b)^4 + (58/243 : ℝ) * (b - a)^1 * (c - b)^5 + (22/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (22*a^6/729 + 32*a^5*b/243 + 14*a^5*c/243 - 10*a^4*b^2/243 + 58*a^4*b*c/243 + 35*a^4*c^2/243 - 19*a^3*b^3/729 - 40*a^3*b^2*c/243 + 23*a^3*b*c^2/243 - 19*a^3*c^3/729 + 35*a^2*b^4/243 + 23*a^2*b^3*c/243 - 113*a^2*b^2*c^2/81 - 40*a^2*b*c^3/243 - 10*a^2*c^4/243 + 14*a*b^5/243 + 58*a*b^4*c/243 - 40*a*b^3*c^2/243 + 23*a*b^2*c^3/243 + 58*a*b*c^4/243 + 32*a*c^5/243 + 22*b^6/729 + 32*b^5*c/243 - 10*b^4*c^2/243 - 19*b^3*c^3/729 + 35*b^2*c^4/243 + 14*b*c^5/243 + 22*c^6/729) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (8/3 : ℝ) * a^4 * (c - a)^2 + (8/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (8/3 : ℝ) * a^4 * (b - c)^2 + (187/27 : ℝ) * a^3 * (c - a)^3 + (89/9 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (94/9 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (101/27 : ℝ) * a^3 * (b - c)^3 + (176/27 : ℝ) * a^2 * (c - a)^4 + (325/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (127/9 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (232/27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (47/27 : ℝ) * a^2 * (b - c)^4 + (23/9 : ℝ) * a^1 * (c - a)^5 + (53/9 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (215/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (59/9 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (8/3 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (10/27 : ℝ) * a^1 * (b - c)^5 + (238/729 : ℝ) * (c - a)^6 + (229/243 : ℝ) * (c - a)^5 * (b - c)^1 + (386/243 : ℝ) * (c - a)^4 * (b - c)^2 + (1261/729 : ℝ) * (c - a)^3 * (b - c)^3 + (260/243 : ℝ) * (c - a)^2 * (b - c)^4 + (76/243 : ℝ) * (c - a)^1 * (b - c)^5 + (22/729 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (22*a^6/729 + 32*a^5*b/243 + 14*a^5*c/243 - 10*a^4*b^2/243 + 58*a^4*b*c/243 + 35*a^4*c^2/243 - 19*a^3*b^3/729 - 40*a^3*b^2*c/243 + 23*a^3*b*c^2/243 - 19*a^3*c^3/729 + 35*a^2*b^4/243 + 23*a^2*b^3*c/243 - 113*a^2*b^2*c^2/81 - 40*a^2*b*c^3/243 - 10*a^2*c^4/243 + 14*a*b^5/243 + 58*a*b^4*c/243 - 40*a*b^3*c^2/243 + 23*a*b^2*c^3/243 + 58*a*b*c^4/243 + 32*a*c^5/243 + 22*b^6/729 + 32*b^5*c/243 - 10*b^4*c^2/243 - 19*b^3*c^3/729 + 35*b^2*c^4/243 + 14*b*c^5/243 + 22*c^6/729) := by
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
  have he : (a^3*c^2 + 2*a^3 + a^2*b^3 - a^2*b^2*c^2 - 2*a^2*b^2 + 2*a^2*b - 2*a^2*c^2 - 4*a^2 + 2*a*c^2 + 4*a + 2*b^3 + b^2*c^3 - 2*b^2*c^2 + 2*b^2*c - 4*b^2 + 4*b + 2*c^3 - 4*c^2 + 4*c - 8) = (22*a^6/729 + 32*a^5*b/243 + 14*a^5*c/243 - 10*a^4*b^2/243 + 58*a^4*b*c/243 + 35*a^4*c^2/243 - 19*a^3*b^3/729 - 40*a^3*b^2*c/243 + 23*a^3*b*c^2/243 - 19*a^3*c^3/729 + 35*a^2*b^4/243 + 23*a^2*b^3*c/243 - 113*a^2*b^2*c^2/81 - 40*a^2*b*c^3/243 - 10*a^2*c^4/243 + 14*a*b^5/243 + 58*a*b^4*c/243 - 40*a*b^3*c^2/243 + 23*a*b^2*c^3/243 + 58*a*b*c^4/243 + 32*a*c^5/243 + 22*b^6/729 + 32*b^5*c/243 - 10*b^4*c^2/243 - 19*b^3*c^3/729 + 35*b^2*c^4/243 + 14*b*c^5/243 + 22*c^6/729) := by
    linear_combination (-22*a^5/729 - 74*a^4*b/729 - 20*a^4*c/729 - 22*a^4/243 + 104*a^3*b^2/729 - 80*a^3*b*c/729 - 52*a^3*b/243 - 85*a^3*c^2/729 + 2*a^3*c/243 - 22*a^3/81 - 85*a^2*b^3/729 + 32*a^2*b^2*c/243 + 52*a^2*b^2/81 + 32*a^2*b*c^2/243 - 10*a^2*b*c/81 - 10*a^2*b/27 + 104*a^2*c^3/729 + 52*a^2*c^2/81 + 8*a^2*c/27 + 32*a^2/27 - 20*a*b^4/729 - 80*a*b^3*c/729 + 2*a*b^3/243 + 32*a*b^2*c^2/243 - 10*a*b^2*c/81 + 8*a*b^2/27 - 80*a*b*c^3/729 - 10*a*b*c^2/81 - 8*a*b*c/27 - 8*a*b/27 - 74*a*c^4/729 - 52*a*c^3/243 - 10*a*c^2/27 - 8*a*c/27 - 4*a/9 - 22*b^5/729 - 74*b^4*c/729 - 22*b^4/243 + 104*b^3*c^2/729 - 52*b^3*c/243 - 22*b^3/81 - 85*b^2*c^3/729 + 52*b^2*c^2/81 - 10*b^2*c/27 + 32*b^2/27 - 20*b*c^4/729 + 2*b*c^3/243 + 8*b*c^2/27 - 8*b*c/27 - 4*b/9 - 22*c^5/729 - 22*c^4/243 - 22*c^3/81 + 32*c^2/27 - 4*c/9 + 8/3) * habc
  have hn : 0 ≤ (a^3*c^2 + 2*a^3 + a^2*b^3 - a^2*b^2*c^2 - 2*a^2*b^2 + 2*a^2*b - 2*a^2*c^2 - 4*a^2 + 2*a*c^2 + 4*a + 2*b^3 + b^2*c^3 - 2*b^2*c^2 + 2*b^2*c - 4*b^2 + 4*b + 2*c^3 - 4*c^2 + 4*c - 8) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a / (b ^ 2 + 2) + b / (c ^ 2 + 2) + c / (a ^ 2 + 2) ≥ 1) := @solution
#print axioms solution
