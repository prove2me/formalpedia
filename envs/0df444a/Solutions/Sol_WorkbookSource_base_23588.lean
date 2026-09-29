-- Prove2me | solution 1 for WorkbookSource.base_23588
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:58:36.756609+00:00
-- url     : https://prove2.me/submissions/dc18a6e8-6bf4-4232-916d-731b2ace9a1f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^2 + b^2 / c^2 + c^2 / a^2 + 8 * (a * b + a * c + b * c) / (a^2 + b^2 + c^2)) ≥ 11  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*c^2 + a^4*b^4 - 10*a^4*b^2*c^2 + a^4*c^4 + 8*a^3*b^3*c^2 + 8*a^3*b^2*c^3 + a^2*b^6 - 10*a^2*b^4*c^2 + 8*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + b^4*c^4 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^6 * (b - a)^2 + (4 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^6 * (c - b)^2 + (20 : ℝ) * a^5 * (b - a)^3 + (42 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (30 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (4 : ℝ) * a^5 * (c - b)^3 + (47 : ℝ) * a^4 * (b - a)^4 + (134 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (131 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (44 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (7 : ℝ) * a^4 * (c - b)^4 + (62 : ℝ) * a^3 * (b - a)^5 + (210 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (268 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (152 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (44 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^3 * (c - b)^5 + (45 : ℝ) * a^2 * (b - a)^6 + (174 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (269 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (208 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (86 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (18 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^2 * (c - b)^6 + (16 : ℝ) * a^1 * (b - a)^7 + (70 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (126 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (120 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (64 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (18 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (b - a)^8 + (10 : ℝ) * (b - a)^7 * (c - b)^1 + (21 : ℝ) * (b - a)^6 * (c - b)^2 + (24 : ℝ) * (b - a)^5 * (c - b)^3 + (16 : ℝ) * (b - a)^4 * (c - b)^4 + (6 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*c^2 + a^4*b^4 - 10*a^4*b^2*c^2 + a^4*c^4 + 8*a^3*b^3*c^2 + 8*a^3*b^2*c^3 + a^2*b^6 - 10*a^2*b^4*c^2 + 8*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + b^4*c^4 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^6 * (c - a)^2 + (4 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (4 : ℝ) * a^6 * (b - c)^2 + (20 : ℝ) * a^5 * (c - a)^3 + (18 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (6 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (4 : ℝ) * a^5 * (b - c)^3 + (47 : ℝ) * a^4 * (c - a)^4 + (54 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (11 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (4 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (7 : ℝ) * a^4 * (b - c)^4 + (62 : ℝ) * a^3 * (c - a)^5 + (100 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (48 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (12 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (14 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (6 : ℝ) * a^3 * (b - c)^5 + (45 : ℝ) * a^2 * (c - a)^6 + (96 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (74 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (28 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (11 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (6 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (1 : ℝ) * a^2 * (b - c)^6 + (16 : ℝ) * a^1 * (c - a)^7 + (42 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (42 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (20 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (4 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (2 : ℝ) * (c - a)^8 + (6 : ℝ) * (c - a)^7 * (b - c)^1 + (7 : ℝ) * (c - a)^6 * (b - c)^2 + (4 : ℝ) * (c - a)^5 * (b - c)^3 + (1 : ℝ) * (c - a)^4 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*c^2 + a^4*b^4 - 10*a^4*b^2*c^2 + a^4*c^4 + 8*a^3*b^3*c^2 + 8*a^3*b^2*c^3 + a^2*b^6 - 10*a^2*b^4*c^2 + 8*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + b^4*c^4 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*c^2 + a^4*b^4 - 10*a^4*b^2*c^2 + a^4*c^4 + 8*a^3*b^3*c^2 + 8*a^3*b^2*c^3 + a^2*b^6 - 10*a^2*b^4*c^2 + 8*a^2*b^3*c^3 - 10*a^2*b^2*c^4 + b^4*c^4 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / b^2 + b^2 / c^2 + c^2 / a^2 + 8 * (a * b + a * c + b * c) / (a^2 + b^2 + c^2)) ≥ 11) := @solution
#print axioms solution
