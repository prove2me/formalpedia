-- Prove2me | solution 1 for WorkbookSource.plus_40002
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:09:05.808659+00:00
-- url     : https://prove2.me/submissions/38ef0630-cd32-4e44-95cb-3bbcb7aabd31

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ (a^2 + b * c - c * a) / (a^2 + a * b + b * c) + (b^2 + c * a - a * b) / (b^2 + b * c + c * a) + (c^2 + a * b - b * c) / (c^2 + c * a + a * b)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b*c + a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c - 2*a^5*b*c^2 - a^5*c^3 - a^4*b^4 - 3*a^4*b^3*c - 2*a^4*b^2*c^2 + a^4*b*c^3 - a^4*c^4 - a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 - 2*a^2*b^5*c - 2*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 2*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 + a*b^3*c^4 - 2*a*b^2*c^5 + a*b*c^6 + 2*b^5*c^3 - b^4*c^4 - b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^6 * (b - a)^2 + (12 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^6 * (c - b)^2 + (43 : ℝ) * a^5 * (b - a)^3 + (48 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (63 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (29 : ℝ) * a^5 * (c - b)^3 + (64 : ℝ) * a^4 * (b - a)^4 + (73 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (112 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (103 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (29 : ℝ) * a^4 * (c - b)^4 + (53 : ℝ) * a^3 * (b - a)^5 + (64 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (98 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (138 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (77 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (13 : ℝ) * a^3 * (c - b)^5 + (27 : ℝ) * a^2 * (b - a)^6 + (41 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (57 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (98 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (80 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (25 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^2 * (c - b)^6 + (8 : ℝ) * a^1 * (b - a)^7 + (17 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (24 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (41 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (42 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (19 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (b - a)^8 + (3 : ℝ) * (b - a)^7 * (c - b)^1 + (5 : ℝ) * (b - a)^6 * (c - b)^2 + (8 : ℝ) * (b - a)^5 * (c - b)^3 + (9 : ℝ) * (b - a)^4 * (c - b)^4 + (5 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*b*c + a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c - 2*a^5*b*c^2 - a^5*c^3 - a^4*b^4 - 3*a^4*b^3*c - 2*a^4*b^2*c^2 + a^4*b*c^3 - a^4*c^4 - a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 - 2*a^2*b^5*c - 2*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 2*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 + a*b^3*c^4 - 2*a*b^2*c^5 + a*b*c^6 + 2*b^5*c^3 - b^4*c^4 - b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^6 * (c - a)^2 + (12 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (12 : ℝ) * a^6 * (b - c)^2 + (43 : ℝ) * a^5 * (c - a)^3 + (81 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (96 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (29 : ℝ) * a^5 * (b - c)^3 + (64 : ℝ) * a^4 * (c - a)^4 + (183 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (277 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (158 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (29 : ℝ) * a^4 * (b - c)^4 + (53 : ℝ) * a^3 * (c - a)^5 + (201 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (372 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (302 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (104 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (13 : ℝ) * a^3 * (b - c)^5 + (27 : ℝ) * a^2 * (c - a)^6 + (121 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (257 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (260 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (123 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (26 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (2 : ℝ) * a^2 * (b - c)^6 + (8 : ℝ) * a^1 * (c - a)^7 + (39 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (90 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (104 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (58 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (14 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (1 : ℝ) * (c - a)^8 + (5 : ℝ) * (c - a)^7 * (b - c)^1 + (12 : ℝ) * (c - a)^6 * (b - c)^2 + (15 : ℝ) * (c - a)^5 * (b - c)^3 + (9 : ℝ) * (c - a)^4 * (b - c)^4 + (2 : ℝ) * (c - a)^3 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b*c + a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c - 2*a^5*b*c^2 - a^5*c^3 - a^4*b^4 - 3*a^4*b^3*c - 2*a^4*b^2*c^2 + a^4*b*c^3 - a^4*c^4 - a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 - 2*a^2*b^5*c - 2*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 2*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 + a*b^3*c^4 - 2*a*b^2*c^5 + a*b*c^6 + 2*b^5*c^3 - b^4*c^4 - b^3*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*b*c + a^6*c^2 + 2*a^5*b^3 + 2*a^5*b^2*c - 2*a^5*b*c^2 - a^5*c^3 - a^4*b^4 - 3*a^4*b^3*c - 2*a^4*b^2*c^2 + a^4*b*c^3 - a^4*c^4 - a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^3*c^5 + a^2*b^6 - 2*a^2*b^5*c - 2*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 2*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - 3*a*b^4*c^3 + a*b^3*c^4 - 2*a*b^2*c^5 + a*b*c^6 + 2*b^5*c^3 - b^4*c^4 - b^3*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ (a^2 + b * c - c * a) / (a^2 + a * b + b * c) + (b^2 + c * a - a * b) / (b^2 + b * c + c * a) + (c^2 + a * b - b * c) / (c^2 + c * a + a * b)) := @solution
#print axioms solution
