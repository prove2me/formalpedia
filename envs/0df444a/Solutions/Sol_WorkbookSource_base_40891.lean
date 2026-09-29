-- Prove2me | solution 1 for WorkbookSource.base_40891
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:15:45.091986+00:00
-- url     : https://prove2.me/submissions/88916eb3-97bc-46cb-9a87-b2e9c4167dd3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b^2 / c)^2 + (b + c^2 / a)^2 + (c + a^2 / b)^2 ≤ (4 * (a^2 + b^2 + c^2)^4) / (27 * a^2 * b^2 * c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^8 + 16*a^6*b^2 - 11*a^6*c^2 + 24*a^4*b^4 + 21*a^4*b^2*c^2 - 54*a^4*b*c^3 + 24*a^4*c^4 - 54*a^3*b^4*c - 11*a^2*b^6 + 21*a^2*b^4*c^2 + 21*a^2*b^2*c^4 + 16*a^2*c^6 - 54*a*b^3*c^4 + 4*b^8 + 16*b^6*c^2 + 24*b^4*c^4 - 11*b^2*c^6 + 4*c^8) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (162 : ℝ) * a^6 * (b - a)^2 + (162 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (162 : ℝ) * a^6 * (c - b)^2 + (642 : ℝ) * a^5 * (b - a)^3 + (558 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (576 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (330 : ℝ) * a^5 * (c - b)^3 + (1150 : ℝ) * a^4 * (b - a)^4 + (950 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (690 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (890 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (370 : ℝ) * a^4 * (c - b)^4 + (1166 : ℝ) * a^3 * (b - a)^5 + (1106 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (448 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (916 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (916 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (254 : ℝ) * a^3 * (c - b)^5 + (705 : ℝ) * a^2 * (b - a)^6 + (900 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (372 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (540 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (933 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (570 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (117 : ℝ) * a^2 * (c - b)^6 + (242 : ℝ) * a^1 * (b - a)^7 + (442 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (318 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (284 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (502 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (474 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (202 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (32 : ℝ) * a^1 * (c - b)^7 + (37 : ℝ) * (b - a)^8 + (94 : ℝ) * (b - a)^7 * (c - b)^1 + (107 : ℝ) * (b - a)^6 * (c - b)^2 + (100 : ℝ) * (b - a)^5 * (c - b)^3 + (139 : ℝ) * (b - a)^4 * (c - b)^4 + (158 : ℝ) * (b - a)^3 * (c - b)^5 + (101 : ℝ) * (b - a)^2 * (c - b)^6 + (32 : ℝ) * (b - a)^1 * (c - b)^7 + (4 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^8 + 16*a^6*b^2 - 11*a^6*c^2 + 24*a^4*b^4 + 21*a^4*b^2*c^2 - 54*a^4*b*c^3 + 24*a^4*c^4 - 54*a^3*b^4*c - 11*a^2*b^6 + 21*a^2*b^4*c^2 + 21*a^2*b^2*c^4 + 16*a^2*c^6 - 54*a*b^3*c^4 + 4*b^8 + 16*b^6*c^2 + 24*b^4*c^4 - 11*b^2*c^6 + 4*c^8) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (162 : ℝ) * a^6 * (c - a)^2 + (162 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (162 : ℝ) * a^6 * (b - c)^2 + (642 : ℝ) * a^5 * (c - a)^3 + (1368 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (1386 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (330 : ℝ) * a^5 * (b - c)^3 + (1150 : ℝ) * a^4 * (c - a)^4 + (3650 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (4740 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (2240 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (370 : ℝ) * a^4 * (b - c)^4 + (1166 : ℝ) * a^3 * (c - a)^5 + (4724 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (7684 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (5452 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (1834 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (254 : ℝ) * a^3 * (b - c)^5 + (705 : ℝ) * a^2 * (c - a)^6 + (3330 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (6447 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (6048 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (3120 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (894 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (117 : ℝ) * a^2 * (b - c)^6 + (242 : ℝ) * a^1 * (c - a)^7 + (1252 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (2748 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (3146 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (2176 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (960 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (256 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (32 : ℝ) * a^1 * (b - c)^7 + (37 : ℝ) * (c - a)^8 + (202 : ℝ) * (c - a)^7 * (b - c)^1 + (485 : ℝ) * (c - a)^6 * (b - c)^2 + (640 : ℝ) * (c - a)^5 * (b - c)^3 + (544 : ℝ) * (c - a)^4 * (b - c)^4 + (320 : ℝ) * (c - a)^3 * (b - c)^5 + (128 : ℝ) * (c - a)^2 * (b - c)^6 + (32 : ℝ) * (c - a)^1 * (b - c)^7 + (4 : ℝ) * (b - c)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^8 + 16*a^6*b^2 - 11*a^6*c^2 + 24*a^4*b^4 + 21*a^4*b^2*c^2 - 54*a^4*b*c^3 + 24*a^4*c^4 - 54*a^3*b^4*c - 11*a^2*b^6 + 21*a^2*b^4*c^2 + 21*a^2*b^2*c^4 + 16*a^2*c^6 - 54*a*b^3*c^4 + 4*b^8 + 16*b^6*c^2 + 24*b^4*c^4 - 11*b^2*c^6 + 4*c^8) := by
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
  have hn : 0 ≤ (4*a^8 + 16*a^6*b^2 - 11*a^6*c^2 + 24*a^4*b^4 + 21*a^4*b^2*c^2 - 54*a^4*b*c^3 + 24*a^4*c^4 - 54*a^3*b^4*c - 11*a^2*b^6 + 21*a^2*b^4*c^2 + 21*a^2*b^2*c^4 + 16*a^2*c^6 - 54*a*b^3*c^4 + 4*b^8 + 16*b^6*c^2 + 24*b^4*c^4 - 11*b^2*c^6 + 4*c^8) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b^2 / c)^2 + (b + c^2 / a)^2 + (c + a^2 / b)^2 ≤ (4 * (a^2 + b^2 + c^2)^4) / (27 * a^2 * b^2 * c^2)) := @solution
#print axioms solution
