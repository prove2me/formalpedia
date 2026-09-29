-- Prove2me | solution 1 for WorkbookSource.plus_44524
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:43.768858+00:00
-- url     : https://prove2.me/submissions/bed62fe5-9628-45dc-b121-f1044b2252c1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (b^2 * c^2 / (a + 3 * b * c) + c^2 * a^2 / (b + 3 * c * a) + a^2 * b^2 / (c + 3 * a * b)) ≤ 3 / 4   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b^2/9 + 82*a^6*b*c/81 + a^6*c^2/9 - 40*a^5*b^2*c/81 - 40*a^5*b*c^2/81 - 2*a^4*b^4/9 + 46*a^4*b^3*c/81 + 704*a^4*b^2*c^2/81 + 46*a^4*b*c^3/81 - 2*a^4*c^4/9 + 46*a^3*b^4*c/81 - 266*a^3*b^3*c^2/27 - 266*a^3*b^2*c^3/27 + 46*a^3*b*c^4/81 + a^2*b^6/9 - 40*a^2*b^5*c/81 + 704*a^2*b^4*c^2/81 - 266*a^2*b^3*c^3/27 + 704*a^2*b^2*c^4/81 - 40*a^2*b*c^5/81 + a^2*c^6/9 + 82*a*b^6*c/81 - 40*a*b^5*c^2/81 + 46*a*b^4*c^3/81 + 46*a*b^3*c^4/81 - 40*a*b^2*c^5/81 + 82*a*b*c^6/81 + b^6*c^2/9 - 2*b^4*c^4/9 + b^2*c^6/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^6 * (b - a)^2 + (16 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^6 * (c - b)^2 + (560/9 : ℝ) * a^5 * (b - a)^3 + (280/3 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (296/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (304/9 : ℝ) * a^5 * (c - b)^3 + (2540/27 : ℝ) * a^4 * (b - a)^4 + (5080/27 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (2020/9 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (3520/27 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (620/27 : ℝ) * a^4 * (c - b)^4 + (5480/81 : ℝ) * a^3 * (b - a)^5 + (13700/81 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (18920/81 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (14680/81 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (5020/81 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (520/81 : ℝ) * a^3 * (c - b)^5 + (1780/81 : ℝ) * a^2 * (b - a)^6 + (1780/27 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (109 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (8758/81 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1523/27 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (40/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (100/81 : ℝ) * a^2 * (c - b)^6 + (176/81 : ℝ) * a^1 * (b - a)^7 + (616/81 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (1420/81 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (670/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1544/81 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (614/81 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (100/81 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4/9 : ℝ) * (b - a)^6 * (c - b)^2 + (4/3 : ℝ) * (b - a)^5 * (c - b)^3 + (13/9 : ℝ) * (b - a)^4 * (c - b)^4 + (2/3 : ℝ) * (b - a)^3 * (c - b)^5 + (1/9 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b^2/9 + 82*a^6*b*c/81 + a^6*c^2/9 - 40*a^5*b^2*c/81 - 40*a^5*b*c^2/81 - 2*a^4*b^4/9 + 46*a^4*b^3*c/81 + 704*a^4*b^2*c^2/81 + 46*a^4*b*c^3/81 - 2*a^4*c^4/9 + 46*a^3*b^4*c/81 - 266*a^3*b^3*c^2/27 - 266*a^3*b^2*c^3/27 + 46*a^3*b*c^4/81 + a^2*b^6/9 - 40*a^2*b^5*c/81 + 704*a^2*b^4*c^2/81 - 266*a^2*b^3*c^3/27 + 704*a^2*b^2*c^4/81 - 40*a^2*b*c^5/81 + a^2*c^6/9 + 82*a*b^6*c/81 - 40*a*b^5*c^2/81 + 46*a*b^4*c^3/81 + 46*a*b^3*c^4/81 - 40*a*b^2*c^5/81 + 82*a*b*c^6/81 + b^6*c^2/9 - 2*b^4*c^4/9 + b^2*c^6/9) := by
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
  have he : (-12*a^4*b^2*c - 12*a^4*b*c^2 - 36*a^3*b^3*c^2 - 4*a^3*b^3 - 36*a^3*b^2*c^3 + 27*a^3*b*c - 4*a^3*c^3 - 12*a^2*b^4*c - 36*a^2*b^3*c^3 + 81*a^2*b^2*c^2 + 9*a^2*b^2 - 12*a^2*b*c^4 + 9*a^2*c^2 - 12*a*b^4*c^2 + 27*a*b^3*c - 12*a*b^2*c^4 + 27*a*b*c^3 + 3*a*b*c - 4*b^3*c^3 + 9*b^2*c^2) = (a^6*b^2/9 + 82*a^6*b*c/81 + a^6*c^2/9 - 40*a^5*b^2*c/81 - 40*a^5*b*c^2/81 - 2*a^4*b^4/9 + 46*a^4*b^3*c/81 + 704*a^4*b^2*c^2/81 + 46*a^4*b*c^3/81 - 2*a^4*c^4/9 + 46*a^3*b^4*c/81 - 266*a^3*b^3*c^2/27 - 266*a^3*b^2*c^3/27 + 46*a^3*b*c^4/81 + a^2*b^6/9 - 40*a^2*b^5*c/81 + 704*a^2*b^4*c^2/81 - 266*a^2*b^3*c^3/27 + 704*a^2*b^2*c^4/81 - 40*a^2*b*c^5/81 + a^2*c^6/9 + 82*a*b^6*c/81 - 40*a*b^5*c^2/81 + 46*a*b^4*c^3/81 + 46*a*b^3*c^4/81 - 40*a*b^2*c^5/81 + 82*a*b*c^6/81 + b^6*c^2/9 - 2*b^4*c^4/9 + b^2*c^6/9) := by
    linear_combination (-a^5*b^2/9 - 82*a^5*b*c/81 - a^5*c^2/9 + a^4*b^3/9 + 131*a^4*b^2*c/81 - a^4*b^2/3 + 131*a^4*b*c^2/81 - 82*a^4*b*c/27 + a^4*c^3/9 - a^4*c^2/3 + a^3*b^4/9 - 62*a^3*b^3*c/27 + 2*a^3*b^3/3 - 322*a^3*b^2*c^2/27 - 34*a^3*b^2*c/9 - a^3*b^2 - 62*a^3*b*c^3/27 - 34*a^3*b*c^2/9 - 82*a^3*b*c/9 + a^3*c^4/9 + 2*a^3*c^3/3 - a^3*c^2 - a^2*b^5/9 + 131*a^2*b^4*c/81 - a^2*b^4/3 - 322*a^2*b^3*c^2/27 - 34*a^2*b^3*c/9 - a^2*b^3 - 322*a^2*b^2*c^3/27 - 254*a^2*b^2*c^2/9 - 11*a^2*b^2*c/9 - 3*a^2*b^2 + 131*a^2*b*c^4/81 - 34*a^2*b*c^3/9 - 11*a^2*b*c^2/9 - a^2*b*c/3 - a^2*c^5/9 - a^2*c^4/3 - a^2*c^3 - 3*a^2*c^2 - 82*a*b^5*c/81 + 131*a*b^4*c^2/81 - 82*a*b^4*c/27 - 62*a*b^3*c^3/27 - 34*a*b^3*c^2/9 - 82*a*b^3*c/9 + 131*a*b^2*c^4/81 - 34*a*b^2*c^3/9 - 11*a*b^2*c^2/9 - a*b^2*c/3 - 82*a*b*c^5/81 - 82*a*b*c^4/27 - 82*a*b*c^3/9 - a*b*c^2/3 - a*b*c - b^5*c^2/9 + b^4*c^3/9 - b^4*c^2/3 + b^3*c^4/9 + 2*b^3*c^3/3 - b^3*c^2 - b^2*c^5/9 - b^2*c^4/3 - b^2*c^3 - 3*b^2*c^2) * habc
  have hn : 0 ≤ (-12*a^4*b^2*c - 12*a^4*b*c^2 - 36*a^3*b^3*c^2 - 4*a^3*b^3 - 36*a^3*b^2*c^3 + 27*a^3*b*c - 4*a^3*c^3 - 12*a^2*b^4*c - 36*a^2*b^3*c^3 + 81*a^2*b^2*c^2 + 9*a^2*b^2 - 12*a^2*b*c^4 + 9*a^2*c^2 - 12*a*b^4*c^2 + 27*a*b^3*c - 12*a*b^2*c^4 + 27*a*b*c^3 + 3*a*b*c - 4*b^3*c^3 + 9*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (b^2 * c^2 / (a + 3 * b * c) + c^2 * a^2 / (b + 3 * c * a) + a^2 * b^2 / (c + 3 * a * b)) ≤ 3 / 4) := @solution
#print axioms solution
