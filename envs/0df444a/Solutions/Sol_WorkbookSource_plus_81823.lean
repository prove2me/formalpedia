-- Prove2me | solution 1 for WorkbookSource.plus_81823
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:57:29.421689+00:00
-- url     : https://prove2.me/submissions/fbccc725-4c88-4a04-9f05-b8c946833690

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + (3 * b + c) ^ 2 / (3 * c + b) ^ 2 + (2 * c + a) ^ 3 / (2 * a + c) ^ 3 ≥ 3   := by
  have hp : 0 ≤ (8*a^4*b^2 + 48*a^4*b*c + 72*a^4*c^2 + 49*a^3*b^3 - 78*a^3*b^2*c - 127*a^3*b*c^2 + 108*a^3*c^3 + 78*a^2*b^3*c - 102*a^2*b^2*c^2 - 222*a^2*b*c^3 + 54*a^2*c^4 + 48*a*b^3*c^2 + a*b^2*c^3 - 42*a*b*c^4 + 9*a*c^5 + 14*b^3*c^3 + 36*b^2*c^4 + 46*b*c^5) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (432 : ℝ) * a^4 * (b - a)^2 + (432 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (432 : ℝ) * a^4 * (c - b)^2 + (1264 : ℝ) * a^3 * (b - a)^3 + (2280 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1848 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (643 : ℝ) * a^3 * (c - b)^3 + (1328 : ℝ) * a^2 * (b - a)^4 + (3488 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (3531 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1694 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (323 : ℝ) * a^2 * (c - b)^4 + (592 : ℝ) * a^1 * (b - a)^5 + (2056 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (2761 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1777 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (535 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (55 : ℝ) * a^1 * (c - b)^5 + (96 : ℝ) * (b - a)^6 + (416 : ℝ) * (b - a)^5 * (c - b)^1 + (718 : ℝ) * (b - a)^4 * (c - b)^2 + (618 : ℝ) * (b - a)^3 * (c - b)^3 + (266 : ℝ) * (b - a)^2 * (c - b)^4 + (46 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (432 : ℝ) * a^4 * (c - a)^2 + (432 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (432 : ℝ) * a^4 * (b - c)^2 + (1264 : ℝ) * a^3 * (c - a)^3 + (1512 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (1080 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (189 : ℝ) * a^3 * (b - c)^3 + (1328 : ℝ) * a^2 * (c - a)^4 + (1824 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (1035 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (216 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (592 : ℝ) * a^1 * (c - a)^5 + (904 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (457 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (90 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (96 : ℝ) * (c - a)^6 + (160 : ℝ) * (c - a)^5 * (b - c)^1 + (78 : ℝ) * (c - a)^4 * (b - c)^2 + (14 : ℝ) * (c - a)^3 * (b - c)^3 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (432 : ℝ) * c^4 * (a - c)^2 + (432 : ℝ) * c^4 * (a - c)^1 * (b - a)^1 + (432 : ℝ) * c^4 * (b - a)^2 + (1085 : ℝ) * c^3 * (a - c)^3 + (1647 : ℝ) * c^3 * (a - c)^2 * (b - a)^1 + (1215 : ℝ) * c^3 * (a - c)^1 * (b - a)^2 + (189 : ℝ) * c^3 * (b - a)^3 + (986 : ℝ) * c^2 * (a - c)^4 + (1947 : ℝ) * c^2 * (a - c)^3 * (b - a)^1 + (1440 : ℝ) * c^2 * (a - c)^2 * (b - a)^2 + (351 : ℝ) * c^2 * (a - c)^1 * (b - a)^3 + (390 : ℝ) * c^1 * (a - c)^5 + (941 : ℝ) * c^1 * (a - c)^4 * (b - a)^1 + (776 : ℝ) * c^1 * (a - c)^3 * (b - a)^2 + (225 : ℝ) * c^1 * (a - c)^2 * (b - a)^3 + (57 : ℝ) * (a - c)^6 + (163 : ℝ) * (a - c)^5 * (b - a)^1 + (155 : ℝ) * (a - c)^4 * (b - a)^2 + (49 : ℝ) * (a - c)^3 * (b - a)^3 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (432 : ℝ) * b^4 * (a - b)^2 + (432 : ℝ) * b^4 * (a - b)^1 * (c - a)^1 + (432 : ℝ) * b^4 * (c - a)^2 + (1539 : ℝ) * b^3 * (a - b)^3 + (2241 : ℝ) * b^3 * (a - b)^2 * (c - a)^1 + (1809 : ℝ) * b^3 * (a - b)^1 * (c - a)^2 + (643 : ℝ) * b^3 * (c - a)^3 + (2025 : ℝ) * b^2 * (a - b)^4 + (3915 : ℝ) * b^2 * (a - b)^3 * (c - a)^1 + (3222 : ℝ) * b^2 * (a - b)^2 * (c - a)^2 + (1527 : ℝ) * b^2 * (a - b)^1 * (c - a)^3 + (323 : ℝ) * b^2 * (c - a)^4 + (1161 : ℝ) * b^1 * (a - b)^5 + (2835 : ℝ) * b^1 * (a - b)^4 * (c - a)^1 + (2655 : ℝ) * b^1 * (a - b)^3 * (c - a)^2 + (1312 : ℝ) * b^1 * (a - b)^2 * (c - a)^3 + (386 : ℝ) * b^1 * (a - b)^1 * (c - a)^4 + (55 : ℝ) * b^1 * (c - a)^5 + (243 : ℝ) * (a - b)^6 + (729 : ℝ) * (a - b)^5 * (c - a)^1 + (810 : ℝ) * (a - b)^4 * (c - a)^2 + (414 : ℝ) * (a - b)^3 * (c - a)^3 + (99 : ℝ) * (a - b)^2 * (c - a)^4 + (9 : ℝ) * (a - b)^1 * (c - a)^5 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (432 : ℝ) * b^4 * (c - b)^2 + (432 : ℝ) * b^4 * (c - b)^1 * (a - c)^1 + (432 : ℝ) * b^4 * (a - c)^2 + (1539 : ℝ) * b^3 * (c - b)^3 + (2376 : ℝ) * b^3 * (c - b)^2 * (a - c)^1 + (1944 : ℝ) * b^3 * (c - b)^1 * (a - c)^2 + (464 : ℝ) * b^3 * (a - c)^3 + (2025 : ℝ) * b^2 * (c - b)^4 + (4185 : ℝ) * b^2 * (c - b)^3 * (a - c)^1 + (3627 : ℝ) * b^2 * (c - b)^2 * (a - c)^2 + (1272 : ℝ) * b^2 * (c - b)^1 * (a - c)^3 + (128 : ℝ) * b^2 * (a - c)^4 + (1161 : ℝ) * b^1 * (c - b)^5 + (2970 : ℝ) * b^1 * (c - b)^4 * (a - c)^1 + (2925 : ℝ) * b^1 * (c - b)^3 * (a - c)^2 + (1253 : ℝ) * b^1 * (c - b)^2 * (a - c)^3 + (192 : ℝ) * b^1 * (c - b)^1 * (a - c)^4 + (243 : ℝ) * (c - b)^6 + (729 : ℝ) * (c - b)^5 * (a - c)^1 + (810 : ℝ) * (c - b)^4 * (a - c)^2 + (396 : ℝ) * (c - b)^3 * (a - c)^3 + (72 : ℝ) * (c - b)^2 * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (432 : ℝ) * c^4 * (b - c)^2 + (432 : ℝ) * c^4 * (b - c)^1 * (a - b)^1 + (432 : ℝ) * c^4 * (a - b)^2 + (1085 : ℝ) * c^3 * (b - c)^3 + (1608 : ℝ) * c^3 * (b - c)^2 * (a - b)^1 + (1176 : ℝ) * c^3 * (b - c)^1 * (a - b)^2 + (464 : ℝ) * c^3 * (a - b)^3 + (986 : ℝ) * c^2 * (b - c)^4 + (1997 : ℝ) * c^2 * (b - c)^3 * (a - b)^1 + (1515 : ℝ) * c^2 * (b - c)^2 * (a - b)^2 + (632 : ℝ) * c^2 * (b - c)^1 * (a - b)^3 + (128 : ℝ) * c^2 * (a - b)^4 + (390 : ℝ) * c^1 * (b - c)^5 + (1009 : ℝ) * c^1 * (b - c)^4 * (a - b)^1 + (912 : ℝ) * c^1 * (b - c)^3 * (a - b)^2 + (357 : ℝ) * c^1 * (b - c)^2 * (a - b)^3 + (64 : ℝ) * c^1 * (b - c)^1 * (a - b)^4 + (57 : ℝ) * (b - c)^6 + (179 : ℝ) * (b - c)^5 * (a - b)^1 + (195 : ℝ) * (b - c)^4 * (a - b)^2 + (81 : ℝ) * (b - c)^3 * (a - b)^3 + (8 : ℝ) * (b - c)^2 * (a - b)^4 := by positivity
          convert hpos using 1 <;> ring
  have hn : 0 ≤ (8*a^4*b^2 + 48*a^4*b*c + 72*a^4*c^2 + 49*a^3*b^3 - 78*a^3*b^2*c - 127*a^3*b*c^2 + 108*a^3*c^3 + 78*a^2*b^3*c - 102*a^2*b^2*c^2 - 222*a^2*b*c^3 + 54*a^2*c^4 + 48*a*b^3*c^2 + a*b^2*c^3 - 42*a*b*c^4 + 9*a*c^5 + 14*b^3*c^3 + 36*b^2*c^4 + 46*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a / b + (3 * b + c) ^ 2 / (3 * c + b) ^ 2 + (2 * c + a) ^ 3 / (2 * a + c) ^ 3 ≥ 3) := @solution
#print axioms solution
