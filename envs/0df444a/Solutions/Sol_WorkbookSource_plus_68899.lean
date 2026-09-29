-- Prove2me | solution 1 for WorkbookSource.plus_68899
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:51:24.981971+00:00
-- url     : https://prove2.me/submissions/d71f6230-68b3-4e2d-987b-1a0f5ae29576

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 + b^2 * c^2) / (c^2 + a^2) + (b^4 + c^2 * a^2) / (a^2 + b^2) + (c^4 + a^2 * b^2) / (b^2 + c^2) ≥ a * b + b * c + c * a   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b^2 + a^6*c^2 - a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - a^5*c^3 + 2*a^4*b^4 - a^4*b^3*c + 3*a^4*b^2*c^2 - a^4*b*c^3 + 2*a^4*c^4 - a^3*b^5 - a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 - a^3*c^5 + a^2*b^6 - a^2*b^5*c + 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 3*a^2*b^2*c^4 - a^2*b*c^5 + 2*a^2*c^6 - a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - a*b^2*c^5 + 2*b^6*c^2 - b^5*c^3 + 2*b^4*c^4 - b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^6 * (b - a)^2 + (16 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^6 * (c - b)^2 + (64 : ℝ) * a^5 * (b - a)^3 + (84 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (84 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (32 : ℝ) * a^5 * (c - b)^3 + (110 : ℝ) * a^4 * (b - a)^4 + (180 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (190 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (120 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (30 : ℝ) * a^4 * (c - b)^4 + (106 : ℝ) * a^3 * (b - a)^5 + (210 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (236 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (184 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (80 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (14 : ℝ) * a^3 * (c - b)^5 + (61 : ℝ) * a^2 * (b - a)^6 + (144 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (175 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (150 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (82 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (24 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (3 : ℝ) * a^2 * (c - b)^6 + (20 : ℝ) * a^1 * (b - a)^7 + (56 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (76 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (70 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (42 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (14 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (3 : ℝ) * (b - a)^8 + (10 : ℝ) * (b - a)^7 * (c - b)^1 + (16 : ℝ) * (b - a)^6 * (c - b)^2 + (17 : ℝ) * (b - a)^5 * (c - b)^3 + (12 : ℝ) * (b - a)^4 * (c - b)^4 + (5 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^6*b^2 + a^6*c^2 - a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - a^5*c^3 + 2*a^4*b^4 - a^4*b^3*c + 3*a^4*b^2*c^2 - a^4*b*c^3 + 2*a^4*c^4 - a^3*b^5 - a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 - a^3*c^5 + a^2*b^6 - a^2*b^5*c + 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 3*a^2*b^2*c^4 - a^2*b*c^5 + 2*a^2*c^6 - a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - a*b^2*c^5 + 2*b^6*c^2 - b^5*c^3 + 2*b^4*c^4 - b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^6 * (c - a)^2 + (16 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (16 : ℝ) * a^6 * (b - c)^2 + (64 : ℝ) * a^5 * (c - a)^3 + (108 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (108 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (32 : ℝ) * a^5 * (b - c)^3 + (110 : ℝ) * a^4 * (c - a)^4 + (260 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (310 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (160 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (30 : ℝ) * a^4 * (b - c)^4 + (106 : ℝ) * a^3 * (c - a)^5 + (320 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (456 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (324 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (110 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (14 : ℝ) * a^3 * (b - c)^5 + (61 : ℝ) * a^2 * (c - a)^6 + (222 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (370 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (330 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (157 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (36 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (3 : ℝ) * a^2 * (b - c)^6 + (20 : ℝ) * a^1 * (c - a)^7 + (84 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (160 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (170 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (102 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (32 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (4 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (3 : ℝ) * (c - a)^8 + (14 : ℝ) * (c - a)^7 * (b - c)^1 + (30 : ℝ) * (c - a)^6 * (b - c)^2 + (37 : ℝ) * (c - a)^5 * (b - c)^3 + (27 : ℝ) * (c - a)^4 * (b - c)^4 + (11 : ℝ) * (c - a)^3 * (b - c)^5 + (2 : ℝ) * (c - a)^2 * (b - c)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b^2 + a^6*c^2 - a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - a^5*c^3 + 2*a^4*b^4 - a^4*b^3*c + 3*a^4*b^2*c^2 - a^4*b*c^3 + 2*a^4*c^4 - a^3*b^5 - a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 - a^3*c^5 + a^2*b^6 - a^2*b^5*c + 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 3*a^2*b^2*c^4 - a^2*b*c^5 + 2*a^2*c^6 - a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - a*b^2*c^5 + 2*b^6*c^2 - b^5*c^3 + 2*b^4*c^4 - b^3*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (2*a^6*b^2 + a^6*c^2 - a^5*b^3 - a^5*b^2*c - a^5*b*c^2 - a^5*c^3 + 2*a^4*b^4 - a^4*b^3*c + 3*a^4*b^2*c^2 - a^4*b*c^3 + 2*a^4*c^4 - a^3*b^5 - a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 - a^3*c^5 + a^2*b^6 - a^2*b^5*c + 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 + 3*a^2*b^2*c^4 - a^2*b*c^5 + 2*a^2*c^6 - a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 - a*b^2*c^5 + 2*b^6*c^2 - b^5*c^3 + 2*b^4*c^4 - b^3*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^4 + b^2 * c^2) / (c^2 + a^2) + (b^4 + c^2 * a^2) / (a^2 + b^2) + (c^4 + a^2 * b^2) / (b^2 + c^2) ≥ a * b + b * c + c * a) := @solution
#print axioms solution
