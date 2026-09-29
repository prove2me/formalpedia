-- Prove2me | solution 1 for WorkbookSource.base_55370
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:28:52.684807+00:00
-- url     : https://prove2.me/submissions/55e8e0d4-33fc-4bea-8a92-025595a6214c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^2 / (7 * a^2 + 9 * a + b * c) + b^2 / (7 * b^2 + 9 * b + c * a) + c^2 / (7 * c^2 + 9 * c + a * b) ≤ 3 / 17  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (39*a^4*b^2 + 130*a^4*b*c + 39*a^4*c^2 - 13*a^3*b^3 + 153*a^3*b^2*c + 153*a^3*b*c^2 - 13*a^3*c^3 + 39*a^2*b^4 + 153*a^2*b^3*c - 1503*a^2*b^2*c^2 + 153*a^2*b*c^3 + 39*a^2*c^4 + 130*a*b^4*c + 153*a*b^3*c^2 + 153*a*b^2*c^3 + 130*a*b*c^4 + 39*b^4*c^2 - 13*b^3*c^3 + 39*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (969 : ℝ) * a^4 * (b - a)^2 + (969 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (969 : ℝ) * a^4 * (c - b)^2 + (2764 : ℝ) * a^3 * (b - a)^3 + (4146 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (3606 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (1112 : ℝ) * a^3 * (c - b)^3 + (2686 : ℝ) * a^2 * (b - a)^4 + (5372 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (4770 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (2084 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (208 : ℝ) * a^2 * (c - b)^4 + (956 : ℝ) * a^1 * (b - a)^5 + (2390 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (2328 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1102 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (208 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (65 : ℝ) * (b - a)^6 + (195 : ℝ) * (b - a)^5 * (c - b)^1 + (234 : ℝ) * (b - a)^4 * (c - b)^2 + (143 : ℝ) * (b - a)^3 * (c - b)^3 + (39 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (39*a^4*b^2 + 130*a^4*b*c + 39*a^4*c^2 - 13*a^3*b^3 + 153*a^3*b^2*c + 153*a^3*b*c^2 - 13*a^3*c^3 + 39*a^2*b^4 + 153*a^2*b^3*c - 1503*a^2*b^2*c^2 + 153*a^2*b*c^3 + 39*a^2*c^4 + 130*a*b^4*c + 153*a*b^3*c^2 + 153*a*b^2*c^3 + 130*a*b*c^4 + 39*b^4*c^2 - 13*b^3*c^3 + 39*b^2*c^4) := by
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
  have he : (4*a^4*b*c - 91*a^3*b^3 + 36*a^3*b^2 + 27*a^3*b*c - 91*a^3*c^3 + 36*a^3*c^2 + 36*a^2*b^3 - 1467*a^2*b^2*c^2 - 819*a^2*b^2*c + 243*a^2*b^2 - 819*a^2*b*c^2 + 324*a^2*b*c + 36*a^2*c^3 + 243*a^2*c^2 + 4*a*b^4*c + 27*a*b^3*c - 819*a*b^2*c^2 + 324*a*b^2*c + 4*a*b*c^4 + 27*a*b*c^3 + 324*a*b*c^2 + 2187*a*b*c - 91*b^3*c^3 + 36*b^3*c^2 + 36*b^2*c^3 + 243*b^2*c^2) = (39*a^4*b^2 + 130*a^4*b*c + 39*a^4*c^2 - 13*a^3*b^3 + 153*a^3*b^2*c + 153*a^3*b*c^2 - 13*a^3*c^3 + 39*a^2*b^4 + 153*a^2*b^3*c - 1503*a^2*b^2*c^2 + 153*a^2*b*c^3 + 39*a^2*c^4 + 130*a*b^4*c + 153*a*b^3*c^2 + 153*a*b^2*c^3 + 130*a*b*c^4 + 39*b^4*c^2 - 13*b^3*c^3 + 39*b^2*c^4) := by
    linear_combination (-39*a^3*b^2 - 126*a^3*b*c - 39*a^3*c^2 - 39*a^2*b^3 + 12*a^2*b^2*c - 81*a^2*b^2 + 12*a^2*b*c^2 - 351*a^2*b*c - 39*a^2*c^3 - 81*a^2*c^2 - 126*a*b^3*c + 12*a*b^2*c^2 - 351*a*b^2*c - 126*a*b*c^3 - 351*a*b*c^2 - 729*a*b*c - 39*b^3*c^2 - 39*b^2*c^3 - 81*b^2*c^2) * hab
  have hn : 0 ≤ (4*a^4*b*c - 91*a^3*b^3 + 36*a^3*b^2 + 27*a^3*b*c - 91*a^3*c^3 + 36*a^3*c^2 + 36*a^2*b^3 - 1467*a^2*b^2*c^2 - 819*a^2*b^2*c + 243*a^2*b^2 - 819*a^2*b*c^2 + 324*a^2*b*c + 36*a^2*c^3 + 243*a^2*c^2 + 4*a*b^4*c + 27*a*b^3*c - 819*a*b^2*c^2 + 324*a*b^2*c + 4*a*b*c^4 + 27*a*b*c^3 + 324*a*b*c^2 + 2187*a*b*c - 91*b^3*c^3 + 36*b^3*c^2 + 36*b^2*c^3 + 243*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a^2 / (7 * a^2 + 9 * a + b * c) + b^2 / (7 * b^2 + 9 * b + c * a) + c^2 / (7 * c^2 + 9 * c + a * b) ≤ 3 / 17) := @solution
#print axioms solution
