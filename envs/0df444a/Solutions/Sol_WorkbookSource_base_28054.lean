-- Prove2me | solution 1 for WorkbookSource.base_28054
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:17.807983+00:00
-- url     : https://prove2.me/submissions/c8a5d358-3e6d-44e6-9cdf-9172e49d98f2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 + b^5) / (b * c^2) + (b^5 + c^5) / (c * a^2) + (c^5 + a^5) / (a * b^2) ≥ 2 * (a^2 + b^2 + c^2)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7*b + a^6*c^2 - 2*a^4*b^2*c^2 + a^2*b^6 - 2*a^2*b^4*c^2 - 2*a^2*b^2*c^4 + a*c^7 + b^7*c + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^6 * (b - a)^2 + (21 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (21 : ℝ) * a^6 * (c - b)^2 + (79 : ℝ) * a^5 * (b - a)^3 + (120 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (135 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (47 : ℝ) * a^5 * (c - b)^3 + (128 : ℝ) * a^4 * (b - a)^4 + (261 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (349 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (216 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (48 : ℝ) * a^4 * (c - b)^4 + (115 : ℝ) * a^3 * (b - a)^5 + (290 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (454 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (386 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (161 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (27 : ℝ) * a^3 * (c - b)^5 + (60 : ℝ) * a^2 * (b - a)^6 + (177 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (316 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (332 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (193 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (60 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (8 : ℝ) * a^2 * (c - b)^6 + (17 : ℝ) * a^1 * (b - a)^7 + (56 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (111 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (135 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (95 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (39 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (9 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1 : ℝ) * a^1 * (c - b)^7 + (2 : ℝ) * (b - a)^8 + (7 : ℝ) * (b - a)^7 * (c - b)^1 + (15 : ℝ) * (b - a)^6 * (c - b)^2 + (20 : ℝ) * (b - a)^5 * (c - b)^3 + (15 : ℝ) * (b - a)^4 * (c - b)^4 + (6 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^7*b + a^6*c^2 - 2*a^4*b^2*c^2 + a^2*b^6 - 2*a^2*b^4*c^2 - 2*a^2*b^2*c^4 + a*c^7 + b^7*c + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^6 * (c - a)^2 + (21 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (21 : ℝ) * a^6 * (b - c)^2 + (79 : ℝ) * a^5 * (c - a)^3 + (117 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (132 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (47 : ℝ) * a^5 * (b - c)^3 + (128 : ℝ) * a^4 * (c - a)^4 + (251 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (334 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (211 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (48 : ℝ) * a^4 * (b - c)^4 + (115 : ℝ) * a^3 * (c - a)^5 + (285 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (444 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (386 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (166 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (27 : ℝ) * a^3 * (b - c)^5 + (60 : ℝ) * a^2 * (c - a)^6 + (183 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (331 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (362 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (223 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (69 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (8 : ℝ) * a^2 * (b - c)^6 + (17 : ℝ) * a^1 * (c - a)^7 + (63 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (132 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (175 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (140 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (63 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (14 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (1 : ℝ) * a^1 * (b - c)^7 + (2 : ℝ) * (c - a)^8 + (9 : ℝ) * (c - a)^7 * (b - c)^1 + (22 : ℝ) * (c - a)^6 * (b - c)^2 + (35 : ℝ) * (c - a)^5 * (b - c)^3 + (35 : ℝ) * (c - a)^4 * (b - c)^4 + (21 : ℝ) * (c - a)^3 * (b - c)^5 + (7 : ℝ) * (c - a)^2 * (b - c)^6 + (1 : ℝ) * (c - a)^1 * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7*b + a^6*c^2 - 2*a^4*b^2*c^2 + a^2*b^6 - 2*a^2*b^4*c^2 - 2*a^2*b^2*c^4 + a*c^7 + b^7*c + b^2*c^6) := by
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
  have hn : 0 ≤ (a^7*b + a^6*c^2 - 2*a^4*b^2*c^2 + a^2*b^6 - 2*a^2*b^4*c^2 - 2*a^2*b^2*c^4 + a*c^7 + b^7*c + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^5 + b^5) / (b * c^2) + (b^5 + c^5) / (c * a^2) + (c^5 + a^5) / (a * b^2) ≥ 2 * (a^2 + b^2 + c^2)) := @solution
#print axioms solution
