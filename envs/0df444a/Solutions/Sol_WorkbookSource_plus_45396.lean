-- Prove2me | solution 1 for WorkbookSource.plus_45396
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:16:58.070649+00:00
-- url     : https://prove2.me/submissions/5acbe425-9707-4c85-ad0b-71831b4bbead

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 / b / c^2 + b^5 / c / a^2 + c^5 / a / b^2 ≥ a^2 + b^2 + c^2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7*b - a^4*b^2*c^2 - a^2*b^4*c^2 - a^2*b^2*c^4 + a*c^7 + b^7*c) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (13 : ℝ) * a^6 * (b - a)^2 + (13 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (13 : ℝ) * a^6 * (c - b)^2 + (47 : ℝ) * a^5 * (b - a)^3 + (60 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (75 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (31 : ℝ) * a^5 * (c - b)^3 + (74 : ℝ) * a^4 * (b - a)^4 + (113 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (167 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (128 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (34 : ℝ) * a^4 * (c - b)^4 + (65 : ℝ) * a^3 * (b - a)^5 + (110 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (182 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (198 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (103 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (21 : ℝ) * a^3 * (c - b)^5 + (33 : ℝ) * a^2 * (b - a)^6 + (57 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (98 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (136 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (104 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (42 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (7 : ℝ) * a^2 * (c - b)^6 + (9 : ℝ) * a^1 * (b - a)^7 + (14 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (21 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (35 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (35 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (21 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (7 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1 : ℝ) * a^1 * (c - b)^7 + (1 : ℝ) * (b - a)^8 + (1 : ℝ) * (b - a)^7 * (c - b)^1 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^7*b - a^4*b^2*c^2 - a^2*b^4*c^2 - a^2*b^2*c^4 + a*c^7 + b^7*c) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (13 : ℝ) * a^6 * (c - a)^2 + (13 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (13 : ℝ) * a^6 * (b - c)^2 + (47 : ℝ) * a^5 * (c - a)^3 + (81 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (96 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (31 : ℝ) * a^5 * (b - c)^3 + (74 : ℝ) * a^4 * (c - a)^4 + (183 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (272 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (163 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (34 : ℝ) * a^4 * (b - c)^4 + (65 : ℝ) * a^3 * (c - a)^5 + (215 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (392 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (338 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (138 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (21 : ℝ) * a^3 * (b - c)^5 + (33 : ℝ) * a^2 * (c - a)^6 + (141 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (308 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (346 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (209 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (63 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (7 : ℝ) * a^2 * (b - c)^6 + (9 : ℝ) * a^1 * (c - a)^7 + (49 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (126 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (175 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (140 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (63 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (14 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (1 : ℝ) * a^1 * (b - c)^7 + (1 : ℝ) * (c - a)^8 + (7 : ℝ) * (c - a)^7 * (b - c)^1 + (21 : ℝ) * (c - a)^6 * (b - c)^2 + (35 : ℝ) * (c - a)^5 * (b - c)^3 + (35 : ℝ) * (c - a)^4 * (b - c)^4 + (21 : ℝ) * (c - a)^3 * (b - c)^5 + (7 : ℝ) * (c - a)^2 * (b - c)^6 + (1 : ℝ) * (c - a)^1 * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7*b - a^4*b^2*c^2 - a^2*b^4*c^2 - a^2*b^2*c^4 + a*c^7 + b^7*c) := by
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
  have hn : 0 ≤ (a^7*b - a^4*b^2*c^2 - a^2*b^4*c^2 - a^2*b^2*c^4 + a*c^7 + b^7*c) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^5 / b / c^2 + b^5 / c / a^2 + c^5 / a / b^2 ≥ a^2 + b^2 + c^2) := @solution
#print axioms solution
