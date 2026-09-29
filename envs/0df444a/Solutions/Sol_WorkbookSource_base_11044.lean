-- Prove2me | solution 1 for WorkbookSource.base_11044
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:34:35.880207+00:00
-- url     : https://prove2.me/submissions/452b9278-b2fc-4469-9b9a-0b61f366f45e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 6) : a^3 / (a^2 + b + c) + b^3 / (b^2 + c + a) + c^3 / (c^2 + a + b) ≥ 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7/72 + 11*a^6*b/432 + 11*a^6*c/432 + 31*a^5*b^2/432 - a^5*b*c/108 + 31*a^5*c^2/432 + 5*a^4*b^3/27 - 67*a^4*b^2*c/432 - 67*a^4*b*c^2/432 + 5*a^4*c^3/27 + 5*a^3*b^4/27 - 13*a^3*b^3*c/54 - a^3*b^2*c^2/54 - 13*a^3*b*c^3/54 + 5*a^3*c^4/27 + 31*a^2*b^5/432 - 67*a^2*b^4*c/432 - a^2*b^3*c^2/54 - a^2*b^2*c^3/54 - 67*a^2*b*c^4/432 + 31*a^2*c^5/432 + 11*a*b^6/432 - a*b^5*c/108 - 67*a*b^4*c^2/432 - 13*a*b^3*c^3/54 - 67*a*b^2*c^4/432 - a*b*c^5/108 + 11*a*c^6/432 + b^7/72 + 11*b^6*c/432 + 31*b^5*c^2/432 + 5*b^4*c^3/27 + 5*b^3*c^4/27 + 31*b^2*c^5/432 + 11*b*c^6/432 + c^7/72) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (13/6 : ℝ) * a^5 * (b - a)^2 + (13/6 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (13/6 : ℝ) * a^5 * (c - b)^2 + (63/8 : ℝ) * a^4 * (b - a)^3 + (189/16 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (473/48 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (71/24 : ℝ) * a^4 * (c - b)^3 + (319/27 : ℝ) * a^3 * (b - a)^4 + (638/27 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (781/36 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (1067/108 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (107/54 : ℝ) * a^3 * (c - b)^4 + (493/54 : ℝ) * a^2 * (b - a)^5 + (2465/108 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (2693/108 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (3149/216 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (1037/216 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (79/108 : ℝ) * a^2 * (c - b)^5 + (98/27 : ℝ) * a^1 * (b - a)^6 + (98/9 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (763/54 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (91/9 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (53/12 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (127/108 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (4/27 : ℝ) * a^1 * (c - b)^6 + (16/27 : ℝ) * (b - a)^7 + (56/27 : ℝ) * (b - a)^6 * (c - b)^1 + (169/54 : ℝ) * (b - a)^5 * (c - b)^2 + (95/36 : ℝ) * (b - a)^4 * (c - b)^3 + (305/216 : ℝ) * (b - a)^3 * (c - b)^4 + (223/432 : ℝ) * (b - a)^2 * (c - b)^5 + (53/432 : ℝ) * (b - a)^1 * (c - b)^6 + (1/72 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7/72 + 11*a^6*b/432 + 11*a^6*c/432 + 31*a^5*b^2/432 - a^5*b*c/108 + 31*a^5*c^2/432 + 5*a^4*b^3/27 - 67*a^4*b^2*c/432 - 67*a^4*b*c^2/432 + 5*a^4*c^3/27 + 5*a^3*b^4/27 - 13*a^3*b^3*c/54 - a^3*b^2*c^2/54 - 13*a^3*b*c^3/54 + 5*a^3*c^4/27 + 31*a^2*b^5/432 - 67*a^2*b^4*c/432 - a^2*b^3*c^2/54 - a^2*b^2*c^3/54 - 67*a^2*b*c^4/432 + 31*a^2*c^5/432 + 11*a*b^6/432 - a*b^5*c/108 - 67*a*b^4*c^2/432 - 13*a*b^3*c^3/54 - 67*a*b^2*c^4/432 - a*b*c^5/108 + 11*a*c^6/432 + b^7/72 + 11*b^6*c/432 + 31*b^5*c^2/432 + 5*b^4*c^3/27 + 5*b^3*c^4/27 + 31*b^2*c^5/432 + 11*b*c^6/432 + c^7/72) := by
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
  have he : (a^5 + a^4*b^2 + a^4*b + a^4*c^2 + a^4*c - 3*a^4 + 2*a^3*b^3 + a^3*b^2*c^2 - 3*a^3*b^2 + a^3*b*c - 3*a^3*b + 2*a^3*c^3 - 3*a^3*c^2 - 3*a^3*c + a^2*b^4 + a^2*b^3*c^2 - 3*a^2*b^3 + a^2*b^2*c^3 - 3*a^2*b^2*c^2 - 3*a^2*b*c - 3*a^2*b + a^2*c^4 - 3*a^2*c^3 - 3*a^2*c + a*b^4 + a*b^3*c - 3*a*b^3 - 3*a*b^2*c - 3*a*b^2 + a*b*c^3 - 3*a*b*c^2 - 6*a*b*c + a*c^4 - 3*a*c^3 - 3*a*c^2 + b^5 + b^4*c^2 + b^4*c - 3*b^4 + 2*b^3*c^3 - 3*b^3*c^2 - 3*b^3*c + b^2*c^4 - 3*b^2*c^3 - 3*b^2*c + b*c^4 - 3*b*c^3 - 3*b*c^2 + c^5 - 3*c^4) = (a^7/72 + 11*a^6*b/432 + 11*a^6*c/432 + 31*a^5*b^2/432 - a^5*b*c/108 + 31*a^5*c^2/432 + 5*a^4*b^3/27 - 67*a^4*b^2*c/432 - 67*a^4*b*c^2/432 + 5*a^4*c^3/27 + 5*a^3*b^4/27 - 13*a^3*b^3*c/54 - a^3*b^2*c^2/54 - 13*a^3*b*c^3/54 + 5*a^3*c^4/27 + 31*a^2*b^5/432 - 67*a^2*b^4*c/432 - a^2*b^3*c^2/54 - a^2*b^2*c^3/54 - 67*a^2*b*c^4/432 + 31*a^2*c^5/432 + 11*a*b^6/432 - a*b^5*c/108 - 67*a*b^4*c^2/432 - 13*a*b^3*c^3/54 - 67*a*b^2*c^4/432 - a*b*c^5/108 + 11*a*c^6/432 + b^7/72 + 11*b^6*c/432 + 31*b^5*c^2/432 + 5*b^4*c^3/27 + 5*b^3*c^4/27 + 31*b^2*c^5/432 + 11*b*c^6/432 + c^7/72) := by
    linear_combination (-a^6/72 - 5*a^5*b/432 - 5*a^5*c/432 - a^5/12 - 13*a^4*b^2/216 + 7*a^4*b*c/216 + a^4*b/72 - 13*a^4*c^2/216 + a^4*c/72 + a^4/2 - a^3*b^3/8 + 79*a^3*b^2*c/432 + 5*a^3*b^2/8 + 79*a^3*b*c^2/432 + a^3*b*c/6 + 7*a^3*b/12 - a^3*c^3/8 + 5*a^3*c^2/8 + 7*a^3*c/12 - 13*a^2*b^4/216 + 79*a^2*b^3*c/432 + 5*a^2*b^3/8 + 47*a^2*b^2*c^2/72 + 11*a^2*b^2*c/36 + a^2*b^2/6 + 79*a^2*b*c^3/432 + 11*a^2*b*c^2/36 + 5*a^2*b*c/6 + a^2*b/2 - 13*a^2*c^4/216 + 5*a^2*c^3/8 + a^2*c^2/6 + a^2*c/2 - 5*a*b^5/432 + 7*a*b^4*c/216 + a*b^4/72 + 79*a*b^3*c^2/432 + a*b^3*c/6 + 7*a*b^3/12 + 79*a*b^2*c^3/432 + 11*a*b^2*c^2/36 + 5*a*b^2*c/6 + a*b^2/2 + 7*a*b*c^4/216 + a*b*c^3/6 + 5*a*b*c^2/6 + a*b*c - 5*a*c^5/432 + a*c^4/72 + 7*a*c^3/12 + a*c^2/2 - b^6/72 - 5*b^5*c/432 - b^5/12 - 13*b^4*c^2/216 + b^4*c/72 + b^4/2 - b^3*c^3/8 + 5*b^3*c^2/8 + 7*b^3*c/12 - 13*b^2*c^4/216 + 5*b^2*c^3/8 + b^2*c^2/6 + b^2*c/2 - 5*b*c^5/432 + b*c^4/72 + 7*b*c^3/12 + b*c^2/2 - c^6/72 - c^5/12 + c^4/2) * hab
  have hn : 0 ≤ (a^5 + a^4*b^2 + a^4*b + a^4*c^2 + a^4*c - 3*a^4 + 2*a^3*b^3 + a^3*b^2*c^2 - 3*a^3*b^2 + a^3*b*c - 3*a^3*b + 2*a^3*c^3 - 3*a^3*c^2 - 3*a^3*c + a^2*b^4 + a^2*b^3*c^2 - 3*a^2*b^3 + a^2*b^2*c^3 - 3*a^2*b^2*c^2 - 3*a^2*b*c - 3*a^2*b + a^2*c^4 - 3*a^2*c^3 - 3*a^2*c + a*b^4 + a*b^3*c - 3*a*b^3 - 3*a*b^2*c - 3*a*b^2 + a*b*c^3 - 3*a*b*c^2 - 6*a*b*c + a*c^4 - 3*a*c^3 - 3*a*c^2 + b^5 + b^4*c^2 + b^4*c - 3*b^4 + 2*b^3*c^3 - 3*b^3*c^2 - 3*b^3*c + b^2*c^4 - 3*b^2*c^3 - 3*b^2*c + b*c^4 - 3*b*c^3 - 3*b*c^2 + c^5 - 3*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 6), a^3 / (a^2 + b + c) + b^3 / (b^2 + c + a) + c^3 / (c^2 + a + b) ≥ 3) := @solution
#print axioms solution
