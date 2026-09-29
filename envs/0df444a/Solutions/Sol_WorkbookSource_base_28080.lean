-- Prove2me | solution 1 for WorkbookSource.base_28080
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:18.746785+00:00
-- url     : https://prove2.me/submissions/12914a2e-ecf5-45e6-8c2d-0c27be43f3cc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) / (2 * a + b + c) ^ 2 + (b + c) * (c + a) / (2 * b + c + a) ^ 2 + (c + a) * (a + b) / (2 * c + a + b) ^ 2 ≤ (a + b + c) ^ 2 / (4 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^8 + 20*a^7*b + 20*a^7*c + 21*a^6*b^2 + 66*a^6*b*c + 53*a^6*c^2 + 100*a^5*b*c^2 + 68*a^5*c^3 + 26*a^4*b^4 - 78*a^4*b^3*c - 104*a^4*b^2*c^2 + 22*a^4*b*c^3 + 26*a^4*c^4 + 68*a^3*b^5 + 22*a^3*b^4*c - 218*a^3*b^3*c^2 - 218*a^3*b^2*c^3 - 78*a^3*b*c^4 + 53*a^2*b^6 + 100*a^2*b^5*c - 104*a^2*b^4*c^2 - 218*a^2*b^3*c^3 - 104*a^2*b^2*c^4 + 21*a^2*c^6 + 20*a*b^7 + 66*a*b^6*c - 78*a*b^4*c^3 + 22*a*b^3*c^4 + 100*a*b^2*c^5 + 66*a*b*c^6 + 20*a*c^7 + 4*b^8 + 20*b^7*c + 21*b^6*c^2 + 26*b^4*c^4 + 68*b^3*c^5 + 53*b^2*c^6 + 20*b*c^7 + 4*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (2560 : ℝ) * a^6 * (b - a)^2 + (2560 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (2560 : ℝ) * a^6 * (c - b)^2 + (10112 : ℝ) * a^5 * (b - a)^3 + (16512 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (16896 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (5248 : ℝ) * a^5 * (c - b)^3 + (16672 : ℝ) * a^4 * (b - a)^4 + (37824 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (45536 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (24384 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (4512 : ℝ) * a^4 * (c - b)^4 + (14696 : ℝ) * a^3 * (b - a)^5 + (42560 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (61152 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (44688 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (15544 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (2072 : ℝ) * a^3 * (c - b)^5 + (7308 : ℝ) * a^2 * (b - a)^6 + (25600 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (43233 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (39586 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (19693 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (5048 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (532 : ℝ) * a^2 * (c - b)^6 + (1944 : ℝ) * a^1 * (b - a)^7 + (7928 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (15412 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (16870 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (10776 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (4006 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (816 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (72 : ℝ) * a^1 * (c - b)^7 + (216 : ℝ) * (b - a)^8 + (996 : ℝ) * (b - a)^7 * (c - b)^1 + (2184 : ℝ) * (b - a)^6 * (c - b)^2 + (2768 : ℝ) * (b - a)^5 * (c - b)^3 + (2141 : ℝ) * (b - a)^4 * (c - b)^4 + (1030 : ℝ) * (b - a)^3 * (c - b)^5 + (305 : ℝ) * (b - a)^2 * (c - b)^6 + (52 : ℝ) * (b - a)^1 * (c - b)^7 + (4 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^8 + 20*a^7*b + 20*a^7*c + 21*a^6*b^2 + 66*a^6*b*c + 53*a^6*c^2 + 100*a^5*b*c^2 + 68*a^5*c^3 + 26*a^4*b^4 - 78*a^4*b^3*c - 104*a^4*b^2*c^2 + 22*a^4*b*c^3 + 26*a^4*c^4 + 68*a^3*b^5 + 22*a^3*b^4*c - 218*a^3*b^3*c^2 - 218*a^3*b^2*c^3 - 78*a^3*b*c^4 + 53*a^2*b^6 + 100*a^2*b^5*c - 104*a^2*b^4*c^2 - 218*a^2*b^3*c^3 - 104*a^2*b^2*c^4 + 21*a^2*c^6 + 20*a*b^7 + 66*a*b^6*c - 78*a*b^4*c^3 + 22*a*b^3*c^4 + 100*a*b^2*c^5 + 66*a*b*c^6 + 20*a*c^7 + 4*b^8 + 20*b^7*c + 21*b^6*c^2 + 26*b^4*c^4 + 68*b^3*c^5 + 53*b^2*c^6 + 20*b*c^7 + 4*c^8) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (2560 : ℝ) * a^6 * (c - a)^2 + (2560 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (2560 : ℝ) * a^6 * (b - c)^2 + (10112 : ℝ) * a^5 * (c - a)^3 + (13824 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (14208 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (5248 : ℝ) * a^5 * (b - c)^3 + (16672 : ℝ) * a^4 * (c - a)^4 + (28864 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (32096 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (19904 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (4512 : ℝ) * a^4 * (b - c)^4 + (14696 : ℝ) * a^3 * (c - a)^5 + (30920 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (37872 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (30368 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (12864 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (2072 : ℝ) * a^3 * (b - c)^5 + (7308 : ℝ) * a^2 * (c - a)^6 + (18248 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (24853 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (23506 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (13953 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (4360 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (532 : ℝ) * a^2 * (b - c)^6 + (1944 : ℝ) * a^1 * (c - a)^7 + (5680 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (8668 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (9310 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (6896 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (3126 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (752 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (72 : ℝ) * a^1 * (b - c)^7 + (216 : ℝ) * (c - a)^8 + (732 : ℝ) * (c - a)^7 * (b - c)^1 + (1260 : ℝ) * (c - a)^6 * (b - c)^2 + (1516 : ℝ) * (c - a)^5 * (b - c)^3 + (1321 : ℝ) * (c - a)^4 * (b - c)^4 + (770 : ℝ) * (c - a)^3 * (b - c)^5 + (273 : ℝ) * (c - a)^2 * (b - c)^6 + (52 : ℝ) * (c - a)^1 * (b - c)^7 + (4 : ℝ) * (b - c)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^8 + 20*a^7*b + 20*a^7*c + 21*a^6*b^2 + 66*a^6*b*c + 53*a^6*c^2 + 100*a^5*b*c^2 + 68*a^5*c^3 + 26*a^4*b^4 - 78*a^4*b^3*c - 104*a^4*b^2*c^2 + 22*a^4*b*c^3 + 26*a^4*c^4 + 68*a^3*b^5 + 22*a^3*b^4*c - 218*a^3*b^3*c^2 - 218*a^3*b^2*c^3 - 78*a^3*b*c^4 + 53*a^2*b^6 + 100*a^2*b^5*c - 104*a^2*b^4*c^2 - 218*a^2*b^3*c^3 - 104*a^2*b^2*c^4 + 21*a^2*c^6 + 20*a*b^7 + 66*a*b^6*c - 78*a*b^4*c^3 + 22*a*b^3*c^4 + 100*a*b^2*c^5 + 66*a*b*c^6 + 20*a*c^7 + 4*b^8 + 20*b^7*c + 21*b^6*c^2 + 26*b^4*c^4 + 68*b^3*c^5 + 53*b^2*c^6 + 20*b*c^7 + 4*c^8) := by
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
  have hn : 0 ≤ (4*a^8 + 20*a^7*b + 20*a^7*c + 21*a^6*b^2 + 66*a^6*b*c + 53*a^6*c^2 + 100*a^5*b*c^2 + 68*a^5*c^3 + 26*a^4*b^4 - 78*a^4*b^3*c - 104*a^4*b^2*c^2 + 22*a^4*b*c^3 + 26*a^4*c^4 + 68*a^3*b^5 + 22*a^3*b^4*c - 218*a^3*b^3*c^2 - 218*a^3*b^2*c^3 - 78*a^3*b*c^4 + 53*a^2*b^6 + 100*a^2*b^5*c - 104*a^2*b^4*c^2 - 218*a^2*b^3*c^3 - 104*a^2*b^2*c^4 + 21*a^2*c^6 + 20*a*b^7 + 66*a*b^6*c - 78*a*b^4*c^3 + 22*a*b^3*c^4 + 100*a*b^2*c^5 + 66*a*b*c^6 + 20*a*c^7 + 4*b^8 + 20*b^7*c + 21*b^6*c^2 + 26*b^4*c^4 + 68*b^3*c^5 + 53*b^2*c^6 + 20*b*c^7 + 4*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) * (b + c) / (2 * a + b + c) ^ 2 + (b + c) * (c + a) / (2 * b + c + a) ^ 2 + (c + a) * (a + b) / (2 * c + a + b) ^ 2 ≤ (a + b + c) ^ 2 / (4 * (a * b + b * c + c * a))) := @solution
#print axioms solution
