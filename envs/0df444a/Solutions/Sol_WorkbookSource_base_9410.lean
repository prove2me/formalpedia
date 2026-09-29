-- Prove2me | solution 1 for WorkbookSource.base_9410
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:29:56.269821+00:00
-- url     : https://prove2.me/submissions/b29cb7bd-6e61-41dd-baa3-b88e76a563ff

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 * b / (a^2 + b) + b^2 * c / (b^2 + c) + c^2 * a / (c^2 + a)) ≤ (a^2 + b^2 + c^2) / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7*c/9 + a^6*b^2/3 + 5*a^6*b*c/27 + 2*a^6*c^2/9 + 2*a^5*b^3/9 + 2*a^5*b^2*c/9 + a^5*b*c^2/9 + a^5*c^3/3 + a^4*b^4/9 - 16*a^4*b^3*c/27 + 2*a^4*b^2*c^2/9 - 4*a^4*b*c^3/27 + a^4*c^4/9 + a^3*b^5/3 - 4*a^3*b^4*c/27 - 4*a^3*b^3*c^2/3 - 4*a^3*b^2*c^3/3 - 16*a^3*b*c^4/27 + 2*a^3*c^5/9 + 2*a^2*b^6/9 + a^2*b^5*c/9 + 2*a^2*b^4*c^2/9 - 4*a^2*b^3*c^3/3 + 2*a^2*b^2*c^4/9 + 2*a^2*b*c^5/9 + a^2*c^6/3 + a*b^7/9 + 5*a*b^6*c/27 + 2*a*b^5*c^2/9 - 16*a*b^4*c^3/27 - 4*a*b^3*c^4/27 + a*b^2*c^5/9 + 5*a*b*c^6/27 + b^6*c^2/3 + 2*b^5*c^3/9 + b^4*c^4/9 + b^3*c^5/3 + 2*b^2*c^6/9 + b*c^7/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^6 * (b - a)^2 + (12 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^6 * (c - b)^2 + (436/9 : ℝ) * a^5 * (b - a)^3 + (221/3 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (217/3 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (212/9 : ℝ) * a^5 * (c - b)^3 + (2197/27 : ℝ) * a^4 * (b - a)^4 + (4484/27 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1652/9 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (2669/27 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (517/27 : ℝ) * a^4 * (c - b)^4 + (1981/27 : ℝ) * a^3 * (b - a)^5 + (5077/27 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2162/9 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (4562/27 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1586/27 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (23/3 : ℝ) * a^3 * (c - b)^5 + (1022/27 : ℝ) * a^2 * (b - a)^6 + (1051/9 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (172 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (3950/27 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (629/9 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (50/3 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (41/27 : ℝ) * a^2 * (c - b)^6 + (290/27 : ℝ) * a^1 * (b - a)^7 + (1048/27 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (589/9 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1763/27 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (1058/27 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (119/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (59/27 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1/9 : ℝ) * a^1 * (c - b)^7 + (4/3 : ℝ) * (b - a)^8 + (50/9 : ℝ) * (b - a)^7 * (c - b)^1 + (32/3 : ℝ) * (b - a)^6 * (c - b)^2 + (37/3 : ℝ) * (b - a)^5 * (c - b)^3 + (9 : ℝ) * (b - a)^4 * (c - b)^4 + (4 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 + (1/9 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^7*c/9 + a^6*b^2/3 + 5*a^6*b*c/27 + 2*a^6*c^2/9 + 2*a^5*b^3/9 + 2*a^5*b^2*c/9 + a^5*b*c^2/9 + a^5*c^3/3 + a^4*b^4/9 - 16*a^4*b^3*c/27 + 2*a^4*b^2*c^2/9 - 4*a^4*b*c^3/27 + a^4*c^4/9 + a^3*b^5/3 - 4*a^3*b^4*c/27 - 4*a^3*b^3*c^2/3 - 4*a^3*b^2*c^3/3 - 16*a^3*b*c^4/27 + 2*a^3*c^5/9 + 2*a^2*b^6/9 + a^2*b^5*c/9 + 2*a^2*b^4*c^2/9 - 4*a^2*b^3*c^3/3 + 2*a^2*b^2*c^4/9 + 2*a^2*b*c^5/9 + a^2*c^6/3 + a*b^7/9 + 5*a*b^6*c/27 + 2*a*b^5*c^2/9 - 16*a*b^4*c^3/27 - 4*a*b^3*c^4/27 + a*b^2*c^5/9 + 5*a*b*c^6/27 + b^6*c^2/3 + 2*b^5*c^3/9 + b^4*c^4/9 + b^3*c^5/3 + 2*b^2*c^6/9 + b*c^7/9) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^6 * (c - a)^2 + (12 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^6 * (b - c)^2 + (436/9 : ℝ) * a^5 * (c - a)^3 + (215/3 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (211/3 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (212/9 : ℝ) * a^5 * (b - c)^3 + (2197/27 : ℝ) * a^4 * (c - a)^4 + (4304/27 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (1562/9 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (2579/27 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (517/27 : ℝ) * a^4 * (b - c)^4 + (1981/27 : ℝ) * a^3 * (c - a)^5 + (4828/27 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (1996/9 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (4244/27 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (1517/27 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (23/3 : ℝ) * a^3 * (b - c)^5 + (1022/27 : ℝ) * a^2 * (c - a)^6 + (331/3 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (1403/9 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (3536/27 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (63 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (139/9 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (41/27 : ℝ) * a^2 * (b - c)^6 + (290/27 : ℝ) * a^1 * (c - a)^7 + (982/27 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (523/9 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (1502/27 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (866/27 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (31/3 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (44/27 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (1/9 : ℝ) * a^1 * (b - c)^7 + (4/3 : ℝ) * (c - a)^8 + (46/9 : ℝ) * (c - a)^7 * (b - c)^1 + (82/9 : ℝ) * (c - a)^6 * (b - c)^2 + (29/3 : ℝ) * (c - a)^5 * (b - c)^3 + (56/9 : ℝ) * (c - a)^4 * (b - c)^4 + (20/9 : ℝ) * (c - a)^3 * (b - c)^5 + (1/3 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7*c/9 + a^6*b^2/3 + 5*a^6*b*c/27 + 2*a^6*c^2/9 + 2*a^5*b^3/9 + 2*a^5*b^2*c/9 + a^5*b*c^2/9 + a^5*c^3/3 + a^4*b^4/9 - 16*a^4*b^3*c/27 + 2*a^4*b^2*c^2/9 - 4*a^4*b*c^3/27 + a^4*c^4/9 + a^3*b^5/3 - 4*a^3*b^4*c/27 - 4*a^3*b^3*c^2/3 - 4*a^3*b^2*c^3/3 - 16*a^3*b*c^4/27 + 2*a^3*c^5/9 + 2*a^2*b^6/9 + a^2*b^5*c/9 + 2*a^2*b^4*c^2/9 - 4*a^2*b^3*c^3/3 + 2*a^2*b^2*c^4/9 + 2*a^2*b*c^5/9 + a^2*c^6/3 + a*b^7/9 + 5*a*b^6*c/27 + 2*a*b^5*c^2/9 - 16*a*b^4*c^3/27 - 4*a*b^3*c^4/27 + a*b^2*c^5/9 + 5*a*b*c^6/27 + b^6*c^2/3 + 2*b^5*c^3/9 + b^4*c^4/9 + b^3*c^5/3 + 2*b^2*c^6/9 + b*c^7/9) := by
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
  have he : (a^5*b^2 + a^5*c + a^4*b^2*c^2 + a^4*c^3 + a^3*b^4 - a^3*b^3 - a^3*b^2*c^2 - a^3*b^2*c - a^3*b*c - a^3*c^3 + a^2*b^4*c^2 - a^2*b^3*c^2 + a^2*b^2*c^4 - a^2*b^2*c^3 - a^2*b*c^3 + a^2*c^5 + a*b^5 - a*b^3*c^2 - a*b^3*c - a*b*c^3 + b^5*c^2 + b^3*c^4 - b^3*c^3 + b*c^5) = (a^7*c/9 + a^6*b^2/3 + 5*a^6*b*c/27 + 2*a^6*c^2/9 + 2*a^5*b^3/9 + 2*a^5*b^2*c/9 + a^5*b*c^2/9 + a^5*c^3/3 + a^4*b^4/9 - 16*a^4*b^3*c/27 + 2*a^4*b^2*c^2/9 - 4*a^4*b*c^3/27 + a^4*c^4/9 + a^3*b^5/3 - 4*a^3*b^4*c/27 - 4*a^3*b^3*c^2/3 - 4*a^3*b^2*c^3/3 - 16*a^3*b*c^4/27 + 2*a^3*c^5/9 + 2*a^2*b^6/9 + a^2*b^5*c/9 + 2*a^2*b^4*c^2/9 - 4*a^2*b^3*c^3/3 + 2*a^2*b^2*c^4/9 + 2*a^2*b*c^5/9 + a^2*c^6/3 + a*b^7/9 + 5*a*b^6*c/27 + 2*a*b^5*c^2/9 - 16*a*b^4*c^3/27 - 4*a*b^3*c^4/27 + a*b^2*c^5/9 + 5*a*b*c^6/27 + b^6*c^2/3 + 2*b^5*c^3/9 + b^4*c^4/9 + b^3*c^5/3 + 2*b^2*c^6/9 + b*c^7/9) := by
    linear_combination (-a^6*c/9 - a^5*b^2/3 - 2*a^5*b*c/27 - a^5*c^2/9 - a^5*c/3 + a^4*b^3/9 + 5*a^4*b^2*c/27 + 2*a^4*b*c^2/27 + a^4*b*c/9 - 2*a^4*c^3/9 - 2*a^3*b^4/9 + 8*a^3*b^3*c/27 + a^3*b^3/3 + 14*a^3*b^2*c^2/27 + 4*a^3*b^2*c/9 + 8*a^3*b*c^3/27 + a^3*b*c^2/9 + a^3*b*c/3 + a^3*c^4/9 + a^3*c^3/3 - a^2*b^5/9 + 2*a^2*b^4*c/27 + 14*a^2*b^3*c^2/27 + a^2*b^3*c/9 + 14*a^2*b^2*c^3/27 + 5*a^2*b*c^4/27 + 4*a^2*b*c^3/9 - a^2*c^5/3 - a*b^6/9 - 2*a*b^5*c/27 - a*b^5/3 + 5*a*b^4*c^2/27 + a*b^4*c/9 + 8*a*b^3*c^3/27 + 4*a*b^3*c^2/9 + a*b^3*c/3 + 2*a*b^2*c^4/27 + a*b^2*c^3/9 - 2*a*b*c^5/27 + a*b*c^4/9 + a*b*c^3/3 - b^5*c^2/3 + b^4*c^3/9 - 2*b^3*c^4/9 + b^3*c^3/3 - b^2*c^5/9 - b*c^6/9 - b*c^5/3) * hab
  have hn : 0 ≤ (a^5*b^2 + a^5*c + a^4*b^2*c^2 + a^4*c^3 + a^3*b^4 - a^3*b^3 - a^3*b^2*c^2 - a^3*b^2*c - a^3*b*c - a^3*c^3 + a^2*b^4*c^2 - a^2*b^3*c^2 + a^2*b^2*c^4 - a^2*b^2*c^3 - a^2*b*c^3 + a^2*c^5 + a*b^5 - a*b^3*c^2 - a*b^3*c - a*b*c^3 + b^5*c^2 + b^3*c^4 - b^3*c^3 + b*c^5) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (a^2 * b / (a^2 + b) + b^2 * c / (b^2 + c) + c^2 * a / (c^2 + a)) ≤ (a^2 + b^2 + c^2) / 2) := @solution
#print axioms solution
