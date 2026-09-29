-- Prove2me | solution 1 for WorkbookSource.plus_62905
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:40:23.070862+00:00
-- url     : https://prove2.me/submissions/19c2e89c-4b5b-44ef-adfc-1fe1d003bbf9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (2 * a ^ 2 + 3 * a + 1) / (b ^ 2 + 1) + (2 * b ^ 2 + 3 * b + 1) / (c ^ 2 + 1) + (2 * c ^ 2 + 3 * c + 1) / (a ^ 2 + 1) ≥ 9   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (67*a^6/243 + 2*a^5*b/3 + 5*a^5*c/9 - 4*a^4*b^2/27 + 67*a^4*b*c/81 + 71*a^4*c^2/27 - 46*a^3*b^3/243 - 26*a^3*b^2*c/27 - 2*a^3*b*c^2/27 - 46*a^3*c^3/243 + 71*a^2*b^4/27 - 2*a^2*b^3*c/27 - 290*a^2*b^2*c^2/27 - 26*a^2*b*c^3/27 - 4*a^2*c^4/27 + 5*a*b^5/9 + 67*a*b^4*c/81 - 26*a*b^3*c^2/27 - 2*a*b^2*c^3/27 + 67*a*b*c^4/81 + 2*a*c^5/3 + 67*b^6/243 + 2*b^5*c/3 - 4*b^4*c^2/27 - 46*b^3*c^3/243 + 71*b^2*c^4/27 + 5*b*c^5/9 + 67*c^6/243) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (68/3 : ℝ) * a^4 * (b - a)^2 + (68/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (68/3 : ℝ) * a^4 * (c - b)^2 + (550/9 : ℝ) * a^3 * (b - a)^3 + (308/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (302/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (266/9 : ℝ) * a^3 * (c - b)^3 + (548/9 : ℝ) * a^2 * (b - a)^4 + (1294/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (496/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (742/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (122/9 : ℝ) * a^2 * (c - b)^4 + (2125/81 : ℝ) * a^1 * (b - a)^5 + (6406/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (8866/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (6002/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1883/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (233/81 : ℝ) * a^1 * (c - b)^5 + (988/243 : ℝ) * (b - a)^6 + (1195/81 : ℝ) * (b - a)^5 * (c - b)^1 + (2005/81 : ℝ) * (b - a)^4 * (c - b)^2 + (5200/243 : ℝ) * (b - a)^3 * (c - b)^3 + (773/81 : ℝ) * (b - a)^2 * (c - b)^4 + (179/81 : ℝ) * (b - a)^1 * (c - b)^5 + (67/243 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (67*a^6/243 + 2*a^5*b/3 + 5*a^5*c/9 - 4*a^4*b^2/27 + 67*a^4*b*c/81 + 71*a^4*c^2/27 - 46*a^3*b^3/243 - 26*a^3*b^2*c/27 - 2*a^3*b*c^2/27 - 46*a^3*c^3/243 + 71*a^2*b^4/27 - 2*a^2*b^3*c/27 - 290*a^2*b^2*c^2/27 - 26*a^2*b*c^3/27 - 4*a^2*c^4/27 + 5*a*b^5/9 + 67*a*b^4*c/81 - 26*a*b^3*c^2/27 - 2*a*b^2*c^3/27 + 67*a*b*c^4/81 + 2*a*c^5/3 + 67*b^6/243 + 2*b^5*c/3 - 4*b^4*c^2/27 - 46*b^3*c^3/243 + 71*b^2*c^4/27 + 5*b*c^5/9 + 67*c^6/243) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (68/3 : ℝ) * a^4 * (c - a)^2 + (68/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (68/3 : ℝ) * a^4 * (b - c)^2 + (550/9 : ℝ) * a^3 * (c - a)^3 + (242/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (236/3 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (266/9 : ℝ) * a^3 * (b - c)^3 + (548/9 : ℝ) * a^2 * (c - a)^4 + (898/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (298/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (544/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (122/9 : ℝ) * a^2 * (b - c)^4 + (2125/81 : ℝ) * a^1 * (c - a)^5 + (4219/81 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (4492/81 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (3410/81 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1478/81 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (233/81 : ℝ) * a^1 * (b - c)^5 + (988/243 : ℝ) * (c - a)^6 + (781/81 : ℝ) * (c - a)^5 * (b - c)^1 + (970/81 : ℝ) * (c - a)^4 * (b - c)^2 + (2770/243 : ℝ) * (c - a)^3 * (b - c)^3 + (593/81 : ℝ) * (c - a)^2 * (b - c)^4 + (188/81 : ℝ) * (c - a)^1 * (b - c)^5 + (67/243 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (67*a^6/243 + 2*a^5*b/3 + 5*a^5*c/9 - 4*a^4*b^2/27 + 67*a^4*b*c/81 + 71*a^4*c^2/27 - 46*a^3*b^3/243 - 26*a^3*b^2*c/27 - 2*a^3*b*c^2/27 - 46*a^3*c^3/243 + 71*a^2*b^4/27 - 2*a^2*b^3*c/27 - 290*a^2*b^2*c^2/27 - 26*a^2*b*c^3/27 - 4*a^2*c^4/27 + 5*a*b^5/9 + 67*a*b^4*c/81 - 26*a*b^3*c^2/27 - 2*a*b^2*c^3/27 + 67*a*b*c^4/81 + 2*a*c^5/3 + 67*b^6/243 + 2*b^5*c/3 - 4*b^4*c^2/27 - 46*b^3*c^3/243 + 71*b^2*c^4/27 + 5*b*c^5/9 + 67*c^6/243) := by
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
  have he : (2*a^4*c^2 + 2*a^4 + 3*a^3*c^2 + 3*a^3 + 2*a^2*b^4 + 3*a^2*b^3 - 9*a^2*b^2*c^2 - 6*a^2*b^2 + 3*a^2*b - 6*a^2*c^2 - 5*a^2 + 3*a*c^2 + 3*a + 2*b^4 + 3*b^3 + 2*b^2*c^4 + 3*b^2*c^3 - 6*b^2*c^2 + 3*b^2*c - 5*b^2 + 3*b + 2*c^4 + 3*c^3 - 5*c^2 + 3*c - 6) = (67*a^6/243 + 2*a^5*b/3 + 5*a^5*c/9 - 4*a^4*b^2/27 + 67*a^4*b*c/81 + 71*a^4*c^2/27 - 46*a^3*b^3/243 - 26*a^3*b^2*c/27 - 2*a^3*b*c^2/27 - 46*a^3*c^3/243 + 71*a^2*b^4/27 - 2*a^2*b^3*c/27 - 290*a^2*b^2*c^2/27 - 26*a^2*b*c^3/27 - 4*a^2*c^4/27 + 5*a*b^5/9 + 67*a*b^4*c/81 - 26*a*b^3*c^2/27 - 2*a*b^2*c^3/27 + 67*a*b*c^4/81 + 2*a*c^5/3 + 67*b^6/243 + 2*b^5*c/3 - 4*b^4*c^2/27 - 46*b^3*c^3/243 + 71*b^2*c^4/27 + 5*b*c^5/9 + 67*c^6/243) := by
    linear_combination (-67*a^5/243 - 95*a^4*b/243 - 68*a^4*c/243 - 67*a^4/81 + 131*a^3*b^2/243 - 38*a^3*b*c/243 - 28*a^3*b/81 - 85*a^3*c^2/243 - a^3*c/81 - 13*a^3/27 - 85*a^2*b^3/243 + 47*a^2*b^2*c/81 + 53*a^2*b^2/27 + 47*a^2*b*c^2/81 - a^2*b*c/9 - 5*a^2*b/9 + 131*a^2*c^3/243 + 53*a^2*c^2/27 + 4*a^2*c/9 + 14*a^2/9 - 68*a*b^4/243 - 38*a*b^3*c/243 - a*b^3/81 + 47*a*b^2*c^2/81 - a*b^2*c/9 + 4*a*b^2/9 - 38*a*b*c^3/243 - a*b*c^2/9 - 2*a*b*c/9 - 2*a*b/9 - 95*a*c^4/243 - 28*a*c^3/81 - 5*a*c^2/9 - 2*a*c/9 - a/3 - 67*b^5/243 - 95*b^4*c/243 - 67*b^4/81 + 131*b^3*c^2/243 - 28*b^3*c/81 - 13*b^3/27 - 85*b^2*c^3/243 + 53*b^2*c^2/27 - 5*b^2*c/9 + 14*b^2/9 - 68*b*c^4/243 - b*c^3/81 + 4*b*c^2/9 - 2*b*c/9 - b/3 - 67*c^5/243 - 67*c^4/81 - 13*c^3/27 + 14*c^2/9 - c/3 + 2) * hab
  have hn : 0 ≤ (2*a^4*c^2 + 2*a^4 + 3*a^3*c^2 + 3*a^3 + 2*a^2*b^4 + 3*a^2*b^3 - 9*a^2*b^2*c^2 - 6*a^2*b^2 + 3*a^2*b - 6*a^2*c^2 - 5*a^2 + 3*a*c^2 + 3*a + 2*b^4 + 3*b^3 + 2*b^2*c^4 + 3*b^2*c^3 - 6*b^2*c^2 + 3*b^2*c - 5*b^2 + 3*b + 2*c^4 + 3*c^3 - 5*c^2 + 3*c - 6) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (2 * a ^ 2 + 3 * a + 1) / (b ^ 2 + 1) + (2 * b ^ 2 + 3 * b + 1) / (c ^ 2 + 1) + (2 * c ^ 2 + 3 * c + 1) / (a ^ 2 + 1) ≥ 9) := @solution
#print axioms solution
