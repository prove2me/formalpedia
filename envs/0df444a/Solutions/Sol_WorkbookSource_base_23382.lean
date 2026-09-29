-- Prove2me | solution 1 for WorkbookSource.base_23382
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:58:34.788371+00:00
-- url     : https://prove2.me/submissions/f4b5fe21-1889-494b-8b2d-547d41f09f1f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (7 * a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * b * c) + (a * b + 7 * b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * c * a) + (a * b + b * c + 7 * c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b) ≤ 9 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^6 + 9*a^5*b + 9*a^5*c - 21*a^4*b^2 + 30*a^4*b*c - 21*a^4*c^2 + 18*a^3*b^3 - 87*a^3*b^2*c + 21*a^3*b*c^2 + 18*a^3*c^3 - 21*a^2*b^4 + 21*a^2*b^3*c + 99*a^2*b^2*c^2 - 87*a^2*b*c^3 - 21*a^2*c^4 + 9*a*b^5 + 30*a*b^4*c - 87*a*b^3*c^2 + 21*a*b^2*c^3 + 30*a*b*c^4 + 9*a*c^5 + 9*b^6 + 9*b^5*c - 21*b^4*c^2 + 18*b^3*c^3 - 21*b^2*c^4 + 9*b*c^5 + 9*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (144 : ℝ) * a^4 * (b - a)^2 + (144 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (144 : ℝ) * a^4 * (c - b)^2 + (294 : ℝ) * a^3 * (b - a)^3 + (495 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (765 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (282 : ℝ) * a^3 * (c - b)^3 + (231 : ℝ) * a^2 * (b - a)^4 + (570 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (1242 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (903 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (213 : ℝ) * a^2 * (c - b)^4 + (84 : ℝ) * a^1 * (b - a)^5 + (264 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (774 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (843 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (393 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (72 : ℝ) * a^1 * (c - b)^5 + (12 : ℝ) * (b - a)^6 + (36 : ℝ) * (b - a)^5 * (c - b)^1 + (132 : ℝ) * (b - a)^4 * (c - b)^2 + (204 : ℝ) * (b - a)^3 * (c - b)^3 + (159 : ℝ) * (b - a)^2 * (c - b)^4 + (63 : ℝ) * (b - a)^1 * (c - b)^5 + (9 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (9*a^6 + 9*a^5*b + 9*a^5*c - 21*a^4*b^2 + 30*a^4*b*c - 21*a^4*c^2 + 18*a^3*b^3 - 87*a^3*b^2*c + 21*a^3*b*c^2 + 18*a^3*c^3 - 21*a^2*b^4 + 21*a^2*b^3*c + 99*a^2*b^2*c^2 - 87*a^2*b*c^3 - 21*a^2*c^4 + 9*a*b^5 + 30*a*b^4*c - 87*a*b^3*c^2 + 21*a*b^2*c^3 + 30*a*b*c^4 + 9*a*c^5 + 9*b^6 + 9*b^5*c - 21*b^4*c^2 + 18*b^3*c^3 - 21*b^2*c^4 + 9*b*c^5 + 9*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (144 : ℝ) * a^4 * (c - a)^2 + (144 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (144 : ℝ) * a^4 * (b - c)^2 + (294 : ℝ) * a^3 * (c - a)^3 + (387 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (657 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (282 : ℝ) * a^3 * (b - c)^3 + (231 : ℝ) * a^2 * (c - a)^4 + (354 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (918 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (795 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (213 : ℝ) * a^2 * (b - c)^4 + (84 : ℝ) * a^1 * (c - a)^5 + (156 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (558 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (735 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (393 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (72 : ℝ) * a^1 * (b - c)^5 + (12 : ℝ) * (c - a)^6 + (36 : ℝ) * (c - a)^5 * (b - c)^1 + (132 : ℝ) * (c - a)^4 * (b - c)^2 + (204 : ℝ) * (c - a)^3 * (b - c)^3 + (159 : ℝ) * (c - a)^2 * (b - c)^4 + (63 : ℝ) * (c - a)^1 * (b - c)^5 + (9 : ℝ) * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^6 + 9*a^5*b + 9*a^5*c - 21*a^4*b^2 + 30*a^4*b*c - 21*a^4*c^2 + 18*a^3*b^3 - 87*a^3*b^2*c + 21*a^3*b*c^2 + 18*a^3*c^3 - 21*a^2*b^4 + 21*a^2*b^3*c + 99*a^2*b^2*c^2 - 87*a^2*b*c^3 - 21*a^2*c^4 + 9*a*b^5 + 30*a*b^4*c - 87*a*b^3*c^2 + 21*a*b^2*c^3 + 30*a*b*c^4 + 9*a*c^5 + 9*b^6 + 9*b^5*c - 21*b^4*c^2 + 18*b^3*c^3 - 21*b^2*c^4 + 9*b*c^5 + 9*c^6) := by
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
  have hn : 0 ≤ (9*a^6 + 9*a^5*b + 9*a^5*c - 21*a^4*b^2 + 30*a^4*b*c - 21*a^4*c^2 + 18*a^3*b^3 - 87*a^3*b^2*c + 21*a^3*b*c^2 + 18*a^3*c^3 - 21*a^2*b^4 + 21*a^2*b^3*c + 99*a^2*b^2*c^2 - 87*a^2*b*c^3 - 21*a^2*c^4 + 9*a*b^5 + 30*a*b^4*c - 87*a*b^3*c^2 + 21*a*b^2*c^3 + 30*a*b*c^4 + 9*a*c^5 + 9*b^6 + 9*b^5*c - 21*b^4*c^2 + 18*b^3*c^3 - 21*b^2*c^4 + 9*b*c^5 + 9*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1), (7 * a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * b * c) + (a * b + 7 * b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * c * a) + (a * b + b * c + 7 * c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b) ≤ 9 / 2) := @solution
#print axioms solution
