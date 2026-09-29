-- Prove2me | solution 1 for WorkbookSource.base_3999
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:11:35.360605+00:00
-- url     : https://prove2.me/submissions/29fee7de-7243-4dd2-8b59-aad626f96423

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 1 / b + 1 / c + 3 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) ≥ 10 * (1 / (3 * a + b) + 1 / (3 * b + c) + 1 / (3 * c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (9*a^5*b^3 + 18*a^5*b^2*c - 6*a^5*b*c^2 + 3*a^5*c^3 + 12*a^4*b^4 + 3*a^4*b^3*c - 12*a^4*b^2*c^2 - 39*a^4*b*c^3 + 12*a^4*c^4 + 3*a^3*b^5 - 39*a^3*b^4*c + 12*a^3*b^3*c^2 + 12*a^3*b^2*c^3 + 3*a^3*b*c^4 + 9*a^3*c^5 - 6*a^2*b^5*c - 12*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 12*a^2*b^2*c^4 + 18*a^2*b*c^5 + 18*a*b^5*c^2 + 3*a*b^4*c^3 - 39*a*b^3*c^4 - 6*a*b^2*c^5 + 9*b^5*c^3 + 12*b^4*c^4 + 3*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^6 * (b - a)^2 + (96 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^6 * (c - b)^2 + (432 : ℝ) * a^5 * (b - a)^3 + (468 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (324 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (144 : ℝ) * a^5 * (c - b)^3 + (816 : ℝ) * a^4 * (b - a)^4 + (1032 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (468 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (252 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (96 : ℝ) * a^4 * (c - b)^4 + (840 : ℝ) * a^3 * (b - a)^5 + (1353 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (594 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (138 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (105 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * a^3 * (c - b)^5 + (504 : ℝ) * a^2 * (b - a)^6 + (1092 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (732 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (162 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (33 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (15 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (168 : ℝ) * a^1 * (b - a)^7 + (489 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (507 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (222 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (39 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (3 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (24 : ℝ) * (b - a)^8 + (90 : ℝ) * (b - a)^7 * (c - b)^1 + (129 : ℝ) * (b - a)^6 * (c - b)^2 + (87 : ℝ) * (b - a)^5 * (c - b)^3 + (27 : ℝ) * (b - a)^4 * (c - b)^4 + (3 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (9*a^5*b^3 + 18*a^5*b^2*c - 6*a^5*b*c^2 + 3*a^5*c^3 + 12*a^4*b^4 + 3*a^4*b^3*c - 12*a^4*b^2*c^2 - 39*a^4*b*c^3 + 12*a^4*c^4 + 3*a^3*b^5 - 39*a^3*b^4*c + 12*a^3*b^3*c^2 + 12*a^3*b^2*c^3 + 3*a^3*b*c^4 + 9*a^3*c^5 - 6*a^2*b^5*c - 12*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 12*a^2*b^2*c^4 + 18*a^2*b*c^5 + 18*a*b^5*c^2 + 3*a*b^4*c^3 - 39*a*b^3*c^4 - 6*a*b^2*c^5 + 9*b^5*c^3 + 12*b^4*c^4 + 3*b^3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^6 * (c - a)^2 + (96 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (96 : ℝ) * a^6 * (b - c)^2 + (432 : ℝ) * a^5 * (c - a)^3 + (828 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (684 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (144 : ℝ) * a^5 * (b - c)^3 + (816 : ℝ) * a^4 * (c - a)^4 + (2232 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (2268 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (852 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (96 : ℝ) * a^4 * (b - c)^4 + (840 : ℝ) * a^3 * (c - a)^5 + (2847 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (3582 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (1926 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (399 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (24 : ℝ) * a^3 * (b - c)^5 + (504 : ℝ) * a^2 * (c - a)^6 + (1932 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (2832 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (1926 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (579 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (57 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (168 : ℝ) * a^1 * (c - a)^7 + (687 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (1101 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (858 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (321 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (45 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (24 : ℝ) * (c - a)^8 + (102 : ℝ) * (c - a)^7 * (b - c)^1 + (171 : ℝ) * (c - a)^6 * (b - c)^2 + (141 : ℝ) * (c - a)^5 * (b - c)^3 + (57 : ℝ) * (c - a)^4 * (b - c)^4 + (9 : ℝ) * (c - a)^3 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (9*a^5*b^3 + 18*a^5*b^2*c - 6*a^5*b*c^2 + 3*a^5*c^3 + 12*a^4*b^4 + 3*a^4*b^3*c - 12*a^4*b^2*c^2 - 39*a^4*b*c^3 + 12*a^4*c^4 + 3*a^3*b^5 - 39*a^3*b^4*c + 12*a^3*b^3*c^2 + 12*a^3*b^2*c^3 + 3*a^3*b*c^4 + 9*a^3*c^5 - 6*a^2*b^5*c - 12*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 12*a^2*b^2*c^4 + 18*a^2*b*c^5 + 18*a*b^5*c^2 + 3*a*b^4*c^3 - 39*a*b^3*c^4 - 6*a*b^2*c^5 + 9*b^5*c^3 + 12*b^4*c^4 + 3*b^3*c^5) := by
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
  have hn : 0 ≤ (9*a^5*b^3 + 18*a^5*b^2*c - 6*a^5*b*c^2 + 3*a^5*c^3 + 12*a^4*b^4 + 3*a^4*b^3*c - 12*a^4*b^2*c^2 - 39*a^4*b*c^3 + 12*a^4*c^4 + 3*a^3*b^5 - 39*a^3*b^4*c + 12*a^3*b^3*c^2 + 12*a^3*b^2*c^3 + 3*a^3*b*c^4 + 9*a^3*c^5 - 6*a^2*b^5*c - 12*a^2*b^4*c^2 + 12*a^2*b^3*c^3 - 12*a^2*b^2*c^4 + 18*a^2*b*c^5 + 18*a*b^5*c^2 + 3*a*b^4*c^3 - 39*a*b^3*c^4 - 6*a*b^2*c^5 + 9*b^5*c^3 + 12*b^4*c^4 + 3*b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / a + 1 / b + 1 / c + 3 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) ≥ 10 * (1 / (3 * a + b) + 1 / (3 * b + c) + 1 / (3 * c + a))) := @solution
#print axioms solution
