-- Prove2me | solution 1 for WorkbookSource.plus_17197
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:25:04.915011+00:00
-- url     : https://prove2.me/submissions/18500119-744c-4c75-b3eb-c9d05391a827

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + 1) / (b ^ 2 + 1) + (b + 1) / (c ^ 2 + 1) + (c + 1) / (a ^ 2 + 1) ≥ 3   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (7*a^6/243 + 10*a^5*b/81 + 7*a^5*c/81 - 2*a^4*b^2/81 + 25*a^4*b*c/81 + 19*a^4*c^2/81 + 14*a^3*b^3/243 - 2*a^3*b^2*c/81 + 22*a^3*b*c^2/81 + 14*a^3*c^3/243 + 19*a^2*b^4/81 + 22*a^2*b^3*c/81 - 86*a^2*b^2*c^2/27 - 2*a^2*b*c^3/81 - 2*a^2*c^4/81 + 7*a*b^5/81 + 25*a*b^4*c/81 - 2*a*b^3*c^2/81 + 22*a*b^2*c^3/81 + 25*a*b*c^4/81 + 10*a*c^5/81 + 7*b^6/243 + 10*b^5*c/81 - 2*b^4*c^2/81 + 14*b^3*c^3/243 + 19*b^2*c^4/81 + 7*b*c^5/81 + 7*c^6/243) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^4 * (b - a)^2 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^4 * (c - b)^2 + (98/9 : ℝ) * a^3 * (b - a)^3 + (52/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (50/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (46/9 : ℝ) * a^3 * (c - b)^3 + (32/3 : ℝ) * a^2 * (b - a)^4 + (70/3 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (76/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (38/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^2 * (c - b)^4 + (347/81 : ℝ) * a^1 * (b - a)^5 + (962/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1238/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (814/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (253/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (31/81 : ℝ) * a^1 * (c - b)^5 + (130/243 : ℝ) * (b - a)^6 + (145/81 : ℝ) * (b - a)^5 * (c - b)^1 + (77/27 : ℝ) * (b - a)^4 * (c - b)^2 + (592/243 : ℝ) * (b - a)^3 * (c - b)^3 + (89/81 : ℝ) * (b - a)^2 * (c - b)^4 + (7/27 : ℝ) * (b - a)^1 * (c - b)^5 + (7/243 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (7*a^6/243 + 10*a^5*b/81 + 7*a^5*c/81 - 2*a^4*b^2/81 + 25*a^4*b*c/81 + 19*a^4*c^2/81 + 14*a^3*b^3/243 - 2*a^3*b^2*c/81 + 22*a^3*b*c^2/81 + 14*a^3*c^3/243 + 19*a^2*b^4/81 + 22*a^2*b^3*c/81 - 86*a^2*b^2*c^2/27 - 2*a^2*b*c^3/81 - 2*a^2*c^4/81 + 7*a*b^5/81 + 25*a*b^4*c/81 - 2*a*b^3*c^2/81 + 22*a*b^2*c^3/81 + 25*a*b*c^4/81 + 10*a*c^5/81 + 7*b^6/243 + 10*b^5*c/81 - 2*b^4*c^2/81 + 14*b^3*c^3/243 + 19*b^2*c^4/81 + 7*b*c^5/81 + 7*c^6/243) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^4 * (c - a)^2 + (4 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^4 * (b - c)^2 + (98/9 : ℝ) * a^3 * (c - a)^3 + (46/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (44/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (46/9 : ℝ) * a^3 * (b - c)^3 + (32/3 : ℝ) * a^2 * (c - a)^4 + (58/3 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (58/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (32/3 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (2 : ℝ) * a^2 * (b - c)^4 + (347/81 : ℝ) * a^1 * (c - a)^5 + (773/81 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (860/81 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (598/81 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (226/81 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (31/81 : ℝ) * a^1 * (b - c)^5 + (130/243 : ℝ) * (c - a)^6 + (115/81 : ℝ) * (c - a)^5 * (b - c)^1 + (52/27 : ℝ) * (c - a)^4 * (b - c)^2 + (430/243 : ℝ) * (c - a)^3 * (b - c)^3 + (83/81 : ℝ) * (c - a)^2 * (b - c)^4 + (8/27 : ℝ) * (c - a)^1 * (b - c)^5 + (7/243 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (7*a^6/243 + 10*a^5*b/81 + 7*a^5*c/81 - 2*a^4*b^2/81 + 25*a^4*b*c/81 + 19*a^4*c^2/81 + 14*a^3*b^3/243 - 2*a^3*b^2*c/81 + 22*a^3*b*c^2/81 + 14*a^3*c^3/243 + 19*a^2*b^4/81 + 22*a^2*b^3*c/81 - 86*a^2*b^2*c^2/27 - 2*a^2*b*c^3/81 - 2*a^2*c^4/81 + 7*a*b^5/81 + 25*a*b^4*c/81 - 2*a*b^3*c^2/81 + 22*a*b^2*c^3/81 + 25*a*b*c^4/81 + 10*a*c^5/81 + 7*b^6/243 + 10*b^5*c/81 - 2*b^4*c^2/81 + 14*b^3*c^3/243 + 19*b^2*c^4/81 + 7*b*c^5/81 + 7*c^6/243) := by
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
  have he : (a^3*c^2 + a^3 + a^2*b^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2 + a^2*b - 2*a^2*c^2 - a^2 + a*c^2 + a + b^3 + b^2*c^3 - 2*b^2*c^2 + b^2*c - b^2 + b + c^3 - c^2 + c) = (7*a^6/243 + 10*a^5*b/81 + 7*a^5*c/81 - 2*a^4*b^2/81 + 25*a^4*b*c/81 + 19*a^4*c^2/81 + 14*a^3*b^3/243 - 2*a^3*b^2*c/81 + 22*a^3*b*c^2/81 + 14*a^3*c^3/243 + 19*a^2*b^4/81 + 22*a^2*b^3*c/81 - 86*a^2*b^2*c^2/27 - 2*a^2*b*c^3/81 - 2*a^2*c^4/81 + 7*a*b^5/81 + 25*a*b^4*c/81 - 2*a*b^3*c^2/81 + 22*a*b^2*c^3/81 + 25*a*b*c^4/81 + 10*a*c^5/81 + 7*b^6/243 + 10*b^5*c/81 - 2*b^4*c^2/81 + 14*b^3*c^3/243 + 19*b^2*c^4/81 + 7*b*c^5/81 + 7*c^6/243) := by
    linear_combination (-7*a^5/243 - 23*a^4*b/243 - 14*a^4*c/243 - 7*a^4/81 + 29*a^3*b^2/243 - 38*a^3*b*c/243 - 16*a^3*b/81 - 43*a^3*c^2/243 - 7*a^3*c/81 - 7*a^3/27 - 43*a^2*b^3/243 + 5*a^2*b^2*c/81 + 5*a^2*b^2/9 + 5*a^2*b*c^2/81 - 5*a^2*b*c/27 - a^2*b/3 + 29*a^2*c^3/243 + 5*a^2*c^2/9 + 2*a^2/9 - 14*a*b^4/243 - 38*a*b^3*c/243 - 7*a*b^3/81 + 5*a*b^2*c^2/81 - 5*a*b^2*c/27 - 38*a*b*c^3/243 - 5*a*b*c^2/27 - 2*a*b*c/9 - 2*a*b/9 - 23*a*c^4/243 - 16*a*c^3/81 - a*c^2/3 - 2*a*c/9 - a/3 - 7*b^5/243 - 23*b^4*c/243 - 7*b^4/81 + 29*b^3*c^2/243 - 16*b^3*c/81 - 7*b^3/27 - 43*b^2*c^3/243 + 5*b^2*c^2/9 - b^2*c/3 + 2*b^2/9 - 14*b*c^4/243 - 7*b*c^3/81 - 2*b*c/9 - b/3 - 7*c^5/243 - 7*c^4/81 - 7*c^3/27 + 2*c^2/9 - c/3) * habc
  have hn : 0 ≤ (a^3*c^2 + a^3 + a^2*b^3 - 3*a^2*b^2*c^2 - 2*a^2*b^2 + a^2*b - 2*a^2*c^2 - a^2 + a*c^2 + a + b^3 + b^2*c^3 - 2*b^2*c^2 + b^2*c - b^2 + b + c^3 - c^2 + c) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a + 1) / (b ^ 2 + 1) + (b + 1) / (c ^ 2 + 1) + (c + 1) / (a ^ 2 + 1) ≥ 3) := @solution
#print axioms solution
