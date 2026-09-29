-- Prove2me | solution 1 for WorkbookSource.plus_61660
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:44:12.564762+00:00
-- url     : https://prove2.me/submissions/00db57ae-9e45-40be-ac3a-9be998a4776a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) - 2 * a * b * c ≥ 6   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6/729 + 2*a^5*b/243 + 2*a^5*c/243 + 23*a^4*b^2/243 - 32*a^4*b*c/243 + 23*a^4*c^2/243 + 134*a^3*b^3/729 - 52*a^3*b^2*c/243 - 52*a^3*b*c^2/243 + 134*a^3*c^3/729 + 23*a^2*b^4/243 - 52*a^2*b^3*c/243 + 40*a^2*b^2*c^2/81 - 52*a^2*b*c^3/243 + 23*a^2*c^4/243 + 2*a*b^5/243 - 32*a*b^4*c/243 - 52*a*b^3*c^2/243 - 52*a*b^2*c^3/243 - 32*a*b*c^4/243 + 2*a*c^5/243 + 4*b^6/729 + 2*b^5*c/243 + 23*b^4*c^2/243 + 134*b^3*c^3/729 + 23*b^2*c^4/243 + 2*b*c^5/243 + 4*c^6/729) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2/3 : ℝ) * a^4 * (b - a)^2 + (2/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (2/3 : ℝ) * a^4 * (c - b)^2 + (20/9 : ℝ) * a^3 * (b - a)^3 + (10/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (4/9 : ℝ) * a^3 * (c - b)^3 + (26/9 : ℝ) * a^2 * (b - a)^4 + (52/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (4 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (10/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (2/9 : ℝ) * a^2 * (c - b)^4 + (140/81 : ℝ) * a^1 * (b - a)^5 + (350/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (320/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (130/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (28/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4/81 : ℝ) * a^1 * (c - b)^5 + (292/729 : ℝ) * (b - a)^6 + (292/243 : ℝ) * (b - a)^5 * (c - b)^1 + (335/243 : ℝ) * (b - a)^4 * (c - b)^2 + (550/729 : ℝ) * (b - a)^3 * (c - b)^3 + (53/243 : ℝ) * (b - a)^2 * (c - b)^4 + (10/243 : ℝ) * (b - a)^1 * (c - b)^5 + (4/729 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6/729 + 2*a^5*b/243 + 2*a^5*c/243 + 23*a^4*b^2/243 - 32*a^4*b*c/243 + 23*a^4*c^2/243 + 134*a^3*b^3/729 - 52*a^3*b^2*c/243 - 52*a^3*b*c^2/243 + 134*a^3*c^3/729 + 23*a^2*b^4/243 - 52*a^2*b^3*c/243 + 40*a^2*b^2*c^2/81 - 52*a^2*b*c^3/243 + 23*a^2*c^4/243 + 2*a*b^5/243 - 32*a*b^4*c/243 - 52*a*b^3*c^2/243 - 52*a*b^2*c^3/243 - 32*a*b*c^4/243 + 2*a*c^5/243 + 4*b^6/729 + 2*b^5*c/243 + 23*b^4*c^2/243 + 134*b^3*c^3/729 + 23*b^2*c^4/243 + 2*b*c^5/243 + 4*c^6/729) := by
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
  have he : (a^2*b^2*c^2 + a^2*b^2 + a^2*c^2 + a^2 - 2*a*b*c + b^2*c^2 + b^2 + c^2 - 5) = (4*a^6/729 + 2*a^5*b/243 + 2*a^5*c/243 + 23*a^4*b^2/243 - 32*a^4*b*c/243 + 23*a^4*c^2/243 + 134*a^3*b^3/729 - 52*a^3*b^2*c/243 - 52*a^3*b*c^2/243 + 134*a^3*c^3/729 + 23*a^2*b^4/243 - 52*a^2*b^3*c/243 + 40*a^2*b^2*c^2/81 - 52*a^2*b*c^3/243 + 23*a^2*c^4/243 + 2*a*b^5/243 - 32*a*b^4*c/243 - 52*a*b^3*c^2/243 - 52*a*b^2*c^3/243 - 32*a*b*c^4/243 + 2*a*c^5/243 + 4*b^6/729 + 2*b^5*c/243 + 23*b^4*c^2/243 + 134*b^3*c^3/729 + 23*b^2*c^4/243 + 2*b*c^5/243 + 4*c^6/729) := by
    linear_combination (-4*a^5/729 - 2*a^4*b/729 - 2*a^4*c/729 - 4*a^4/243 - 67*a^3*b^2/729 + 100*a^3*b*c/729 + 2*a^3*b/243 - 67*a^3*c^2/729 + 2*a^3*c/243 - 4*a^3/81 - 67*a^2*b^3/729 + 41*a^2*b^2*c/243 - 23*a^2*b^2/81 + 41*a^2*b*c^2/243 + 32*a^2*b*c/81 + 2*a^2*b/27 - 67*a^2*c^3/729 - 23*a^2*c^2/81 + 2*a^2*c/27 - 4*a^2/27 - 2*a*b^4/729 + 100*a*b^3*c/729 + 2*a*b^3/243 + 41*a*b^2*c^2/243 + 32*a*b^2*c/81 + 2*a*b^2/27 + 100*a*b*c^3/729 + 32*a*b*c^2/81 + 28*a*b*c/27 + 10*a*b/27 - 2*a*c^4/729 + 2*a*c^3/243 + 2*a*c^2/27 + 10*a*c/27 + 5*a/9 - 4*b^5/729 - 2*b^4*c/729 - 4*b^4/243 - 67*b^3*c^2/729 + 2*b^3*c/243 - 4*b^3/81 - 67*b^2*c^3/729 - 23*b^2*c^2/81 + 2*b^2*c/27 - 4*b^2/27 - 2*b*c^4/729 + 2*b*c^3/243 + 2*b*c^2/27 + 10*b*c/27 + 5*b/9 - 4*c^5/729 - 4*c^4/243 - 4*c^3/81 - 4*c^2/27 + 5*c/9 + 5/3) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3), (a^2 + 1) * (b^2 + 1) * (c^2 + 1) - 2 * a * b * c ≥ 6) := @solution
#print axioms solution
