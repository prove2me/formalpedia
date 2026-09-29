-- Prove2me | solution 1 for WorkbookSource.base_27098
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:38:37.669707+00:00
-- url     : https://prove2.me/submissions/6e25caef-52a1-4231-8a03-6b9391cf20ff

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + 2 * a / b) ^ 2 + (1 + 2 * b / c) ^ 2 + (1 + 2 * c / a) ^ 2 ≥ 9 * (a + b + c) ^ 2 / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*b*c^2 + 4*a^5*c^3 - 5*a^4*b^2*c^2 + 8*a^4*b*c^3 + 4*a^3*b^5 + 8*a^3*b^4*c - 11*a^3*b^3*c^2 - 11*a^3*b^2*c^3 + 4*a^2*b^5*c - 5*a^2*b^4*c^2 - 11*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + 8*a*b^3*c^4 + 4*a*b^2*c^5 + 4*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (51 : ℝ) * a^6 * (b - a)^2 + (51 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (51 : ℝ) * a^6 * (c - b)^2 + (224 : ℝ) * a^5 * (b - a)^3 + (390 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (330 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (82 : ℝ) * a^5 * (c - b)^3 + (398 : ℝ) * a^4 * (b - a)^4 + (976 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (959 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (381 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (43 : ℝ) * a^4 * (c - b)^4 + (364 : ℝ) * a^3 * (b - a)^5 + (1138 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1364 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (728 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (154 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (8 : ℝ) * a^3 * (c - b)^5 + (179 : ℝ) * a^2 * (b - a)^6 + (673 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (972 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (657 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (199 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (20 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (44 : ℝ) * a^1 * (b - a)^7 + (192 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (328 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (272 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (108 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (4 : ℝ) * (b - a)^8 + (20 : ℝ) * (b - a)^7 * (c - b)^1 + (40 : ℝ) * (b - a)^6 * (c - b)^2 + (40 : ℝ) * (b - a)^5 * (c - b)^3 + (20 : ℝ) * (b - a)^4 * (c - b)^4 + (4 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^5*b*c^2 + 4*a^5*c^3 - 5*a^4*b^2*c^2 + 8*a^4*b*c^3 + 4*a^3*b^5 + 8*a^3*b^4*c - 11*a^3*b^3*c^2 - 11*a^3*b^2*c^3 + 4*a^2*b^5*c - 5*a^2*b^4*c^2 - 11*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + 8*a*b^3*c^4 + 4*a*b^2*c^5 + 4*b^3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (51 : ℝ) * a^6 * (c - a)^2 + (51 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (51 : ℝ) * a^6 * (b - c)^2 + (224 : ℝ) * a^5 * (c - a)^3 + (282 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (222 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (82 : ℝ) * a^5 * (b - c)^3 + (398 : ℝ) * a^4 * (c - a)^4 + (616 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (419 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (201 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (43 : ℝ) * a^4 * (b - c)^4 + (364 : ℝ) * a^3 * (c - a)^5 + (682 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (452 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (176 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (58 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (8 : ℝ) * a^3 * (b - c)^5 + (179 : ℝ) * a^2 * (c - a)^6 + (401 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (292 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (81 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (15 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (4 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (44 : ℝ) * a^1 * (c - a)^7 + (116 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (100 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (28 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (4 : ℝ) * (c - a)^8 + (12 : ℝ) * (c - a)^7 * (b - c)^1 + (12 : ℝ) * (c - a)^6 * (b - c)^2 + (4 : ℝ) * (c - a)^5 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*b*c^2 + 4*a^5*c^3 - 5*a^4*b^2*c^2 + 8*a^4*b*c^3 + 4*a^3*b^5 + 8*a^3*b^4*c - 11*a^3*b^3*c^2 - 11*a^3*b^2*c^3 + 4*a^2*b^5*c - 5*a^2*b^4*c^2 - 11*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + 8*a*b^3*c^4 + 4*a*b^2*c^5 + 4*b^3*c^5) := by
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
  have hn : 0 ≤ (4*a^5*b*c^2 + 4*a^5*c^3 - 5*a^4*b^2*c^2 + 8*a^4*b*c^3 + 4*a^3*b^5 + 8*a^3*b^4*c - 11*a^3*b^3*c^2 - 11*a^3*b^2*c^3 + 4*a^2*b^5*c - 5*a^2*b^4*c^2 - 11*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + 8*a*b^3*c^4 + 4*a*b^2*c^5 + 4*b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 + 2 * a / b) ^ 2 + (1 + 2 * b / c) ^ 2 + (1 + 2 * c / a) ^ 2 ≥ 9 * (a + b + c) ^ 2 / (a * b + b * c + c * a)) := @solution
#print axioms solution
