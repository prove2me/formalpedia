-- Prove2me | solution 1 for WorkbookSource.base_48922
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:10.361475+00:00
-- url     : https://prove2.me/submissions/148cedb1-f702-472f-b45d-81d477c4c656

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (habc : a + b + c = 3) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a * b + 5 * a) / (b ^ 2 + 4 * b + 3) + (3 * b * c + 5 * b) / (c ^ 2 + 4 * c + 3) + (3 * c * a + 5 * c) / (a ^ 2 + 4 * a + 3) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (16*a^6/27 + 52*a^5*b/27 + 38*a^5*c/9 + 8*a^4*b^2/3 + 17*a^4*b*c/3 + 241*a^4*c^2/27 + 179*a^3*b^3/27 - 311*a^3*b^2*c/27 - 41*a^3*b*c^2/9 + 179*a^3*c^3/27 + 241*a^2*b^4/27 - 41*a^2*b^3*c/9 - 131*a^2*b^2*c^2/3 - 311*a^2*b*c^3/27 + 8*a^2*c^4/3 + 38*a*b^5/9 + 17*a*b^4*c/3 - 311*a*b^3*c^2/27 - 41*a*b^2*c^3/9 + 17*a*b*c^4/3 + 52*a*c^5/27 + 16*b^6/27 + 52*b^5*c/27 + 8*b^4*c^2/3 + 179*b^3*c^3/27 + 241*b^2*c^4/27 + 38*b*c^5/9 + 16*c^6/27) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (352/3 : ℝ) * a^4 * (b - a)^2 + (352/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (352/3 : ℝ) * a^4 * (c - b)^2 + (2968/9 : ℝ) * a^3 * (b - a)^3 + (1604/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (484 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (1256/9 : ℝ) * a^3 * (c - b)^3 + (3080/9 : ℝ) * a^2 * (b - a)^4 + (6880/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2356/3 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (3268/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (512/9 : ℝ) * a^2 * (c - b)^4 + (4178/27 : ℝ) * a^1 * (b - a)^5 + (11849/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (14498/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (8818/27 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (2515/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (262/27 : ℝ) * a^1 * (c - b)^5 + (230/9 : ℝ) * (b - a)^6 + (2363/27 : ℝ) * (b - a)^5 * (c - b)^1 + (1145/9 : ℝ) * (b - a)^4 * (c - b)^2 + (2603/27 : ℝ) * (b - a)^3 * (c - b)^3 + (1051/27 : ℝ) * (b - a)^2 * (c - b)^4 + (70/9 : ℝ) * (b - a)^1 * (c - b)^5 + (16/27 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (16*a^6/27 + 52*a^5*b/27 + 38*a^5*c/9 + 8*a^4*b^2/3 + 17*a^4*b*c/3 + 241*a^4*c^2/27 + 179*a^3*b^3/27 - 311*a^3*b^2*c/27 - 41*a^3*b*c^2/9 + 179*a^3*c^3/27 + 241*a^2*b^4/27 - 41*a^2*b^3*c/9 - 131*a^2*b^2*c^2/3 - 311*a^2*b*c^3/27 + 8*a^2*c^4/3 + 38*a*b^5/9 + 17*a*b^4*c/3 - 311*a*b^3*c^2/27 - 41*a*b^2*c^3/9 + 17*a*b*c^4/3 + 52*a*c^5/27 + 16*b^6/27 + 52*b^5*c/27 + 8*b^4*c^2/3 + 179*b^3*c^3/27 + 241*b^2*c^4/27 + 38*b*c^5/9 + 16*c^6/27) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (352/3 : ℝ) * a^4 * (c - a)^2 + (352/3 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (352/3 : ℝ) * a^4 * (b - c)^2 + (2968/9 : ℝ) * a^3 * (c - a)^3 + (1364/3 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (404 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (1256/9 : ℝ) * a^3 * (b - c)^3 + (3080/9 : ℝ) * a^2 * (c - a)^4 + (5440/9 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (1636/3 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (2548/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (512/9 : ℝ) * a^2 * (b - c)^4 + (4178/27 : ℝ) * a^1 * (c - a)^5 + (9041/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (8882/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (5362/27 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (1867/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (262/27 : ℝ) * a^1 * (b - c)^5 + (230/9 : ℝ) * (c - a)^6 + (1777/27 : ℝ) * (c - a)^5 * (b - c)^1 + (1970/27 : ℝ) * (c - a)^4 * (b - c)^2 + (1307/27 : ℝ) * (c - a)^3 * (b - c)^3 + (572/27 : ℝ) * (c - a)^2 * (b - c)^4 + (148/27 : ℝ) * (c - a)^1 * (b - c)^5 + (16/27 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (16*a^6/27 + 52*a^5*b/27 + 38*a^5*c/9 + 8*a^4*b^2/3 + 17*a^4*b*c/3 + 241*a^4*c^2/27 + 179*a^3*b^3/27 - 311*a^3*b^2*c/27 - 41*a^3*b*c^2/9 + 179*a^3*c^3/27 + 241*a^2*b^4/27 - 41*a^2*b^3*c/9 - 131*a^2*b^2*c^2/3 - 311*a^2*b*c^3/27 + 8*a^2*c^4/3 + 38*a*b^5/9 + 17*a*b^4*c/3 - 311*a*b^3*c^2/27 - 41*a*b^2*c^3/9 + 17*a*b*c^4/3 + 52*a*c^5/27 + 16*b^6/27 + 52*b^5*c/27 + 8*b^4*c^2/3 + 179*b^3*c^3/27 + 241*b^2*c^4/27 + 38*b*c^5/9 + 16*c^6/27) := by
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
  have he : (3*a^3*b*c^2 + 12*a^3*b*c + 9*a^3*b + 5*a^3*c^2 + 20*a^3*c + 15*a^3 + 3*a^2*b^3*c + 5*a^2*b^3 - 3*a^2*b^2*c^2 + 11*a^2*b^2 + 9*a^2*b*c + 15*a^2*b + 11*a^2*c^2 + 44*a^2*c + 33*a^2 + 12*a*b^3*c + 20*a*b^3 + 3*a*b^2*c^3 + 9*a*b^2*c + 44*a*b^2 + 12*a*b*c^3 + 9*a*b*c^2 - 84*a*b*c - 57*a*b + 9*a*c^3 + 15*a*c^2 - 57*a*c - 63*a + 9*b^3*c + 15*b^3 + 5*b^2*c^3 + 11*b^2*c^2 + 15*b^2*c + 33*b^2 + 20*b*c^3 + 44*b*c^2 - 57*b*c - 63*b + 15*c^3 + 33*c^2 - 63*c - 81) = (16*a^6/27 + 52*a^5*b/27 + 38*a^5*c/9 + 8*a^4*b^2/3 + 17*a^4*b*c/3 + 241*a^4*c^2/27 + 179*a^3*b^3/27 - 311*a^3*b^2*c/27 - 41*a^3*b*c^2/9 + 179*a^3*c^3/27 + 241*a^2*b^4/27 - 41*a^2*b^3*c/9 - 131*a^2*b^2*c^2/3 - 311*a^2*b*c^3/27 + 8*a^2*c^4/3 + 38*a*b^5/9 + 17*a*b^4*c/3 - 311*a*b^3*c^2/27 - 41*a*b^2*c^3/9 + 17*a*b*c^4/3 + 52*a*c^5/27 + 16*b^6/27 + 52*b^5*c/27 + 8*b^4*c^2/3 + 179*b^3*c^3/27 + 241*b^2*c^4/27 + 38*b*c^5/9 + 16*c^6/27) := by
    linear_combination (-16*a^5/27 - 4*a^4*b/3 - 98*a^4*c/27 - 16*a^4/9 - 4*a^3*b^2/3 - 19*a^3*b*c/27 - 20*a^3*b/9 - 143*a^3*c^2/27 - 82*a^3*c/9 - 16*a^3/3 - 143*a^2*b^3/27 + 122*a^2*b^2*c/9 - 16*a^2*b^2/9 + 122*a^2*b*c^2/9 + 191*a^2*b*c/9 + 23*a^2*b/3 - 4*a^2*c^3/3 - 16*a^2*c^2/9 - 2*a^2*c - a^2 - 98*a*b^4/27 - 19*a*b^3*c/27 - 82*a*b^3/9 + 122*a*b^2*c^2/9 + 191*a*b^2*c/9 - 2*a*b^2 - 19*a*b*c^3/27 + 191*a*b*c^2/9 + 67*a*b*c + 39*a*b - 4*a*c^4/3 - 20*a*c^3/9 + 23*a*c^2/3 + 39*a*c + 30*a - 16*b^5/27 - 4*b^4*c/3 - 16*b^4/9 - 4*b^3*c^2/3 - 20*b^3*c/9 - 16*b^3/3 - 143*b^2*c^3/27 - 16*b^2*c^2/9 + 23*b^2*c/3 - b^2 - 98*b*c^4/27 - 82*b*c^3/9 - 2*b*c^2 + 39*b*c + 30*b - 16*c^5/27 - 16*c^4/9 - 16*c^3/3 - c^2 + 30*c + 27) * habc
  have hn : 0 ≤ (3*a^3*b*c^2 + 12*a^3*b*c + 9*a^3*b + 5*a^3*c^2 + 20*a^3*c + 15*a^3 + 3*a^2*b^3*c + 5*a^2*b^3 - 3*a^2*b^2*c^2 + 11*a^2*b^2 + 9*a^2*b*c + 15*a^2*b + 11*a^2*c^2 + 44*a^2*c + 33*a^2 + 12*a*b^3*c + 20*a*b^3 + 3*a*b^2*c^3 + 9*a*b^2*c + 44*a*b^2 + 12*a*b*c^3 + 9*a*b*c^2 - 84*a*b*c - 57*a*b + 9*a*c^3 + 15*a*c^2 - 57*a*c - 63*a + 9*b^3*c + 15*b^3 + 5*b^2*c^3 + 11*b^2*c^2 + 15*b^2*c + 33*b^2 + 20*b*c^3 + 44*b*c^2 - 57*b*c - 63*b + 15*c^3 + 33*c^2 - 63*c - 81) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (habc : a + b + c = 3) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * a * b + 5 * a) / (b ^ 2 + 4 * b + 3) + (3 * b * c + 5 * b) / (c ^ 2 + 4 * c + 3) + (3 * c * a + 5 * c) / (a ^ 2 + 4 * a + 3) ≥ 3) := @solution
#print axioms solution
