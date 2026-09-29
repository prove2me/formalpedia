-- Prove2me | solution 1 for WorkbookSource.base_8926
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:39:30.879623+00:00
-- url     : https://prove2.me/submissions/501a0cbd-30a1-4e40-9670-a18d0a207dd7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b^2 + 2 * a * b) + b^2 / (c^2 + 2 * b * c) + c^2 / (a^2 + 2 * c * a)) ≥ 3 * (a^2 + b^2 + c^2) / (a + b + c)^2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b*c + a^6*c^2 + 2*a^5*b^3 - 8*a^5*b^2*c + 4*a^5*b*c^2 + 4*a^5*c^3 + 5*a^4*b^4 + 4*a^4*b^3*c - 14*a^4*b^2*c^2 + 4*a^4*b*c^3 + 5*a^4*c^4 + 4*a^3*b^5 + 4*a^3*b^4*c - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 + 4*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 + 4*a^2*b^5*c - 14*a^2*b^4*c^2 - 4*a^2*b^3*c^3 - 14*a^2*b^2*c^4 - 8*a^2*b*c^5 + 2*a*b^6*c - 8*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 + 4*a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 + 5*b^4*c^4 + 4*b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^6 * (b - a)^2 + (72 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (72 : ℝ) * a^6 * (c - b)^2 + (330 : ℝ) * a^5 * (b - a)^3 + (558 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (432 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (102 : ℝ) * a^5 * (c - b)^3 + (629 : ℝ) * a^4 * (b - a)^4 + (1468 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (1317 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (478 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (59 : ℝ) * a^4 * (c - b)^4 + (636 : ℝ) * a^3 * (b - a)^5 + (1860 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (2068 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (1032 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (228 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (20 : ℝ) * a^3 * (c - b)^5 + (357 : ℝ) * a^2 * (b - a)^6 + (1236 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1665 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (1080 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (348 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (54 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (3 : ℝ) * a^2 * (c - b)^6 + (104 : ℝ) * a^1 * (b - a)^7 + (410 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (644 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (510 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (214 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (46 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (12 : ℝ) * (b - a)^8 + (52 : ℝ) * (b - a)^7 * (c - b)^1 + (91 : ℝ) * (b - a)^6 * (c - b)^2 + (82 : ℝ) * (b - a)^5 * (c - b)^3 + (40 : ℝ) * (b - a)^4 * (c - b)^4 + (10 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^6*b*c + a^6*c^2 + 2*a^5*b^3 - 8*a^5*b^2*c + 4*a^5*b*c^2 + 4*a^5*c^3 + 5*a^4*b^4 + 4*a^4*b^3*c - 14*a^4*b^2*c^2 + 4*a^4*b*c^3 + 5*a^4*c^4 + 4*a^3*b^5 + 4*a^3*b^4*c - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 + 4*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 + 4*a^2*b^5*c - 14*a^2*b^4*c^2 - 4*a^2*b^3*c^3 - 14*a^2*b^2*c^4 - 8*a^2*b*c^5 + 2*a*b^6*c - 8*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 + 4*a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 + 5*b^4*c^4 + 4*b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^6 * (c - a)^2 + (72 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (72 : ℝ) * a^6 * (b - c)^2 + (330 : ℝ) * a^5 * (c - a)^3 + (432 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (306 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (102 : ℝ) * a^5 * (b - c)^3 + (629 : ℝ) * a^4 * (c - a)^4 + (1048 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (687 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (268 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (59 : ℝ) * a^4 * (b - c)^4 + (636 : ℝ) * a^3 * (c - a)^5 + (1320 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (988 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (372 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (108 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (20 : ℝ) * a^3 * (b - c)^5 + (357 : ℝ) * a^2 * (c - a)^6 + (906 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (840 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (360 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (93 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (24 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (3 : ℝ) * a^2 * (b - c)^6 + (104 : ℝ) * a^1 * (c - a)^7 + (318 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (368 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (200 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (54 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (10 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (12 : ℝ) * (c - a)^8 + (44 : ℝ) * (c - a)^7 * (b - c)^1 + (63 : ℝ) * (c - a)^6 * (b - c)^2 + (44 : ℝ) * (c - a)^5 * (b - c)^3 + (15 : ℝ) * (c - a)^4 * (b - c)^4 + (2 : ℝ) * (c - a)^3 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b*c + a^6*c^2 + 2*a^5*b^3 - 8*a^5*b^2*c + 4*a^5*b*c^2 + 4*a^5*c^3 + 5*a^4*b^4 + 4*a^4*b^3*c - 14*a^4*b^2*c^2 + 4*a^4*b*c^3 + 5*a^4*c^4 + 4*a^3*b^5 + 4*a^3*b^4*c - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 + 4*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 + 4*a^2*b^5*c - 14*a^2*b^4*c^2 - 4*a^2*b^3*c^3 - 14*a^2*b^2*c^4 - 8*a^2*b*c^5 + 2*a*b^6*c - 8*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 + 4*a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 + 5*b^4*c^4 + 4*b^3*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (2*a^6*b*c + a^6*c^2 + 2*a^5*b^3 - 8*a^5*b^2*c + 4*a^5*b*c^2 + 4*a^5*c^3 + 5*a^4*b^4 + 4*a^4*b^3*c - 14*a^4*b^2*c^2 + 4*a^4*b*c^3 + 5*a^4*c^4 + 4*a^3*b^5 + 4*a^3*b^4*c - 4*a^3*b^3*c^2 - 4*a^3*b^2*c^3 + 4*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 + 4*a^2*b^5*c - 14*a^2*b^4*c^2 - 4*a^2*b^3*c^3 - 14*a^2*b^2*c^4 - 8*a^2*b*c^5 + 2*a*b^6*c - 8*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 + 4*a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 + 5*b^4*c^4 + 4*b^3*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / (b^2 + 2 * a * b) + b^2 / (c^2 + 2 * b * c) + c^2 / (a^2 + 2 * c * a)) ≥ 3 * (a^2 + b^2 + c^2) / (a + b + c)^2) := @solution
#print axioms solution
