-- Prove2me | solution 1 for WorkbookSource.base_32371
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:04.50168+00:00
-- url     : https://prove2.me/submissions/41ad6e53-0cbb-4e0c-8654-16f1d78150d8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3) / (b^2 + c^2) + (b^3 + c^3) / (c^2 + a^2) + (c^3 + a^3) / (a^2 + b^2) ≥ a + b + c  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7 + a^5*b^2 + a^5*c^2 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^7 + b^5*c^2 - b^3*c^4 + b^2*c^5 + c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^5 * (b - a)^2 + (20 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (20 : ℝ) * a^5 * (c - b)^2 + (58 : ℝ) * a^4 * (b - a)^3 + (84 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (110 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (42 : ℝ) * a^4 * (c - b)^3 + (74 : ℝ) * a^3 * (b - a)^4 + (140 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (230 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (164 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (42 : ℝ) * a^3 * (c - b)^4 + (51 : ℝ) * a^2 * (b - a)^5 + (120 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (236 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (240 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (119 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (23 : ℝ) * a^2 * (c - b)^5 + (19 : ℝ) * a^1 * (b - a)^6 + (54 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (123 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (160 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (116 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (44 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (7 : ℝ) * a^1 * (c - b)^6 + (3 : ℝ) * (b - a)^7 + (10 : ℝ) * (b - a)^6 * (c - b)^1 + (26 : ℝ) * (b - a)^5 * (c - b)^2 + (41 : ℝ) * (b - a)^4 * (c - b)^3 + (39 : ℝ) * (b - a)^3 * (c - b)^4 + (22 : ℝ) * (b - a)^2 * (c - b)^5 + (7 : ℝ) * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^7 + a^5*b^2 + a^5*c^2 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^7 + b^5*c^2 - b^3*c^4 + b^2*c^5 + c^7) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^5 * (c - a)^2 + (20 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (20 : ℝ) * a^5 * (b - c)^2 + (58 : ℝ) * a^4 * (c - a)^3 + (90 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (116 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (42 : ℝ) * a^4 * (b - c)^3 + (74 : ℝ) * a^3 * (c - a)^4 + (156 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (254 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (172 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (42 : ℝ) * a^3 * (b - c)^4 + (51 : ℝ) * a^2 * (c - a)^5 + (135 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (266 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (258 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (122 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (23 : ℝ) * a^2 * (b - c)^5 + (19 : ℝ) * a^1 * (c - a)^6 + (60 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (138 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (172 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (119 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (44 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (7 : ℝ) * a^1 * (b - c)^6 + (3 : ℝ) * (c - a)^7 + (11 : ℝ) * (c - a)^6 * (b - c)^1 + (29 : ℝ) * (c - a)^5 * (b - c)^2 + (44 : ℝ) * (c - a)^4 * (b - c)^3 + (40 : ℝ) * (c - a)^3 * (b - c)^4 + (22 : ℝ) * (c - a)^2 * (b - c)^5 + (7 : ℝ) * (c - a)^1 * (b - c)^6 + (1 : ℝ) * (b - c)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7 + a^5*b^2 + a^5*c^2 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^7 + b^5*c^2 - b^3*c^4 + b^2*c^5 + c^7) := by
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
  have hn : 0 ≤ (a^7 + a^5*b^2 + a^5*c^2 - a^4*b^2*c - a^4*b*c^2 - a^4*c^3 - a^3*b^4 + a^2*b^5 - a^2*b^4*c - a^2*b*c^4 + a^2*c^5 - a*b^4*c^2 - a*b^2*c^4 + b^7 + b^5*c^2 - b^3*c^4 + b^2*c^5 + c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3) / (b^2 + c^2) + (b^3 + c^3) / (c^2 + a^2) + (c^3 + a^3) / (a^2 + b^2) ≥ a + b + c) := @solution
#print axioms solution
