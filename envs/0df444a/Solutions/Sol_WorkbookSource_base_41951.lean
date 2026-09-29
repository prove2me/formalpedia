-- Prove2me | solution 1 for WorkbookSource.base_41951
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:15:51.175142+00:00
-- url     : https://prove2.me/submissions/65b5d6d0-5c66-48df-9166-88caedc1e191

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 1 / (a ^ 2 + b ^ 2 + c + 21) + 1 / (b ^ 2 + c ^ 2 + a + 21) + 1 / (c ^ 2 + a ^ 2 + b + 21) ≤ 1 / 8  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (320*a^6/81 + 724*a^5*b/81 + 724*a^5*c/81 + 826*a^4*b^2/81 + 28*a^4*b*c/9 + 826*a^4*c^2/81 + 682*a^3*b^3/81 - 1541*a^3*b^2*c/81 - 1541*a^3*b*c^2/81 + 682*a^3*c^3/81 + 826*a^2*b^4/81 - 1541*a^2*b^3*c/81 - 424*a^2*b^2*c^2/9 - 1541*a^2*b*c^3/81 + 826*a^2*c^4/81 + 724*a*b^5/81 + 28*a*b^4*c/9 - 1541*a*b^3*c^2/81 - 1541*a*b^2*c^3/81 + 28*a*b*c^4/9 + 724*a*c^5/81 + 320*b^6/81 + 724*b^5*c/81 + 826*b^4*c^2/81 + 682*b^3*c^3/81 + 826*b^2*c^4/81 + 724*b*c^5/81 + 320*c^6/81) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (752/3 : ℝ) * a^4 * (b - a)^2 + (752/3 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (752/3 : ℝ) * a^4 * (c - b)^2 + (18146/27 : ℝ) * a^3 * (b - a)^3 + (9073/9 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (8975/9 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (8926/27 : ℝ) * a^3 * (c - b)^3 + (18478/27 : ℝ) * a^2 * (b - a)^4 + (36956/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (13721/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (22685/27 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (4648/27 : ℝ) * a^2 * (c - b)^4 + (25402/81 : ℝ) * a^1 * (b - a)^5 + (63505/81 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (82060/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (59585/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (22364/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (3368/81 : ℝ) * a^1 * (c - b)^5 + (1474/27 : ℝ) * (b - a)^6 + (1474/9 : ℝ) * (b - a)^5 * (c - b)^1 + (19868/81 : ℝ) * (b - a)^4 * (c - b)^2 + (17626/81 : ℝ) * (b - a)^3 * (c - b)^3 + (3082/27 : ℝ) * (b - a)^2 * (c - b)^4 + (2644/81 : ℝ) * (b - a)^1 * (c - b)^5 + (320/81 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (320*a^6/81 + 724*a^5*b/81 + 724*a^5*c/81 + 826*a^4*b^2/81 + 28*a^4*b*c/9 + 826*a^4*c^2/81 + 682*a^3*b^3/81 - 1541*a^3*b^2*c/81 - 1541*a^3*b*c^2/81 + 682*a^3*c^3/81 + 826*a^2*b^4/81 - 1541*a^2*b^3*c/81 - 424*a^2*b^2*c^2/9 - 1541*a^2*b*c^3/81 + 826*a^2*c^4/81 + 724*a*b^5/81 + 28*a*b^4*c/9 - 1541*a*b^3*c^2/81 - 1541*a*b^2*c^3/81 + 28*a*b*c^4/9 + 724*a*c^5/81 + 320*b^6/81 + 724*b^5*c/81 + 826*b^4*c^2/81 + 682*b^3*c^3/81 + 826*b^2*c^4/81 + 724*b*c^5/81 + 320*c^6/81) := by
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
  have he : (a^5 + a^4*b^2 + a^4*c^2 + 13*a^4 + a^3*b^2 + a^3*b + a^3*c^2 + a^3*c + 26*a^3 + a^2*b^4 + a^2*b^3 + 2*a^2*b^2*c^2 + a^2*b^2*c + 39*a^2*b^2 + a^2*b*c^2 + 13*a^2*b + a^2*c^4 + a^2*c^3 + 39*a^2*c^2 + 13*a^2*c + 210*a^2 + a*b^3 + a*b^2*c^2 + 13*a*b^2 + a*b*c + 13*a*b + a*c^3 + 13*a*c^2 + 13*a*c + 105*a + b^5 + b^4*c^2 + 13*b^4 + b^3*c^2 + b^3*c + 26*b^3 + b^2*c^4 + b^2*c^3 + 39*b^2*c^2 + 13*b^2*c + 210*b^2 + b*c^3 + 13*b*c^2 + 13*b*c + 105*b + c^5 + 13*c^4 + 26*c^3 + 210*c^2 + 105*c - 1323) = (320*a^6/81 + 724*a^5*b/81 + 724*a^5*c/81 + 826*a^4*b^2/81 + 28*a^4*b*c/9 + 826*a^4*c^2/81 + 682*a^3*b^3/81 - 1541*a^3*b^2*c/81 - 1541*a^3*b*c^2/81 + 682*a^3*c^3/81 + 826*a^2*b^4/81 - 1541*a^2*b^3*c/81 - 424*a^2*b^2*c^2/9 - 1541*a^2*b*c^3/81 + 826*a^2*c^4/81 + 724*a*b^5/81 + 28*a*b^4*c/9 - 1541*a*b^3*c^2/81 - 1541*a*b^2*c^3/81 + 28*a*b*c^4/9 + 724*a*c^5/81 + 320*b^6/81 + 724*b^5*c/81 + 826*b^4*c^2/81 + 682*b^3*c^3/81 + 826*b^2*c^4/81 + 724*b*c^5/81 + 320*c^6/81) := by
    linear_combination (-320*a^5/81 - 404*a^4*b/81 - 404*a^4*c/81 - 293*a^4/27 - 341*a^3*b^2/81 + 556*a^3*b*c/81 - 37*a^3*b/9 - 341*a^3*c^2/81 - 37*a^3*c/9 - 176*a^3/9 - 341*a^2*b^3/81 + 442*a^2*b^2*c/27 - 203*a^2*b^2/27 + 442*a^2*b*c^2/27 + 778*a^2*b*c/27 + 74*a^2*b/9 - 341*a^2*c^3/81 - 203*a^2*c^2/27 + 74*a^2*c/9 - 98*a^2/3 - 404*a*b^4/81 + 556*a*b^3*c/81 - 37*a*b^3/9 + 442*a*b^2*c^2/27 + 778*a*b^2*c/27 + 74*a*b^2/9 + 556*a*b*c^3/81 + 778*a*b*c^2/27 + 70*a*b*c + 211*a*b/3 - 404*a*c^4/81 - 37*a*c^3/9 + 74*a*c^2/9 + 211*a*c/3 + 112*a - 320*b^5/81 - 404*b^4*c/81 - 293*b^4/27 - 341*b^3*c^2/81 - 37*b^3*c/9 - 176*b^3/9 - 341*b^2*c^3/81 - 203*b^2*c^2/27 + 74*b^2*c/9 - 98*b^2/3 - 404*b*c^4/81 - 37*b*c^3/9 + 74*b*c^2/9 + 211*b*c/3 + 112*b - 320*c^5/81 - 293*c^4/27 - 176*c^3/9 - 98*c^2/3 + 112*c + 441) * hab
  have hn : 0 ≤ (a^5 + a^4*b^2 + a^4*c^2 + 13*a^4 + a^3*b^2 + a^3*b + a^3*c^2 + a^3*c + 26*a^3 + a^2*b^4 + a^2*b^3 + 2*a^2*b^2*c^2 + a^2*b^2*c + 39*a^2*b^2 + a^2*b*c^2 + 13*a^2*b + a^2*c^4 + a^2*c^3 + 39*a^2*c^2 + 13*a^2*c + 210*a^2 + a*b^3 + a*b^2*c^2 + 13*a*b^2 + a*b*c + 13*a*b + a*c^3 + 13*a*c^2 + 13*a*c + 105*a + b^5 + b^4*c^2 + 13*b^4 + b^3*c^2 + b^3*c + 26*b^3 + b^2*c^4 + b^2*c^3 + 39*b^2*c^2 + 13*b^2*c + 210*b^2 + b*c^3 + 13*b*c^2 + 13*b*c + 105*b + c^5 + 13*c^4 + 26*c^3 + 210*c^2 + 105*c - 1323) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 1 / (a ^ 2 + b ^ 2 + c + 21) + 1 / (b ^ 2 + c ^ 2 + a + 21) + 1 / (c ^ 2 + a ^ 2 + b + 21) ≤ 1 / 8) := @solution
#print axioms solution
