-- Prove2me | solution 1 for WorkbookSource.plus_8965
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:54:26.223627+00:00
-- url     : https://prove2.me/submissions/973761c0-fc9d-4086-bc8d-0e073f90a4aa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (1 / (a^2 + a * b) + 1 / (b^2 + b * c) + 1 / (c^2 + c * a)) ≥ 9 / 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 4*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 5*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 5*a^2*b^3*c - 12*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 4*a*b^4*c - 3*a*b^3*c^2 - 5*a*b^2*c^3 + 4*a*b*c^4 + 2*b^4*c^2 + 2*b^3*c^3 + 2*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^4 * (b - a)^2 + (40 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (40 : ℝ) * a^4 * (c - b)^2 + (112 : ℝ) * a^3 * (b - a)^3 + (177 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (161 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (48 : ℝ) * a^3 * (c - b)^3 + (114 : ℝ) * a^2 * (b - a)^4 + (246 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (249 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (117 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (18 : ℝ) * a^2 * (c - b)^4 + (50 : ℝ) * a^1 * (b - a)^5 + (139 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (166 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (101 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (28 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (8 : ℝ) * (b - a)^6 + (28 : ℝ) * (b - a)^5 * (c - b)^1 + (40 : ℝ) * (b - a)^4 * (c - b)^2 + (30 : ℝ) * (b - a)^3 * (c - b)^3 + (12 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 4*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 5*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 5*a^2*b^3*c - 12*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 4*a*b^4*c - 3*a*b^3*c^2 - 5*a*b^2*c^3 + 4*a*b*c^4 + 2*b^4*c^2 + 2*b^3*c^3 + 2*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^4 * (c - a)^2 + (40 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (40 : ℝ) * a^4 * (b - c)^2 + (112 : ℝ) * a^3 * (c - a)^3 + (159 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (143 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (48 : ℝ) * a^3 * (b - c)^3 + (114 : ℝ) * a^2 * (c - a)^4 + (210 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (195 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (99 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (18 : ℝ) * a^2 * (b - c)^4 + (50 : ℝ) * a^1 * (c - a)^5 + (111 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (110 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (63 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (18 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^1 * (b - c)^5 + (8 : ℝ) * (c - a)^6 + (20 : ℝ) * (c - a)^5 * (b - c)^1 + (20 : ℝ) * (c - a)^4 * (b - c)^2 + (10 : ℝ) * (c - a)^3 * (b - c)^3 + (2 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 4*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 5*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 5*a^2*b^3*c - 12*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 4*a*b^4*c - 3*a*b^3*c^2 - 5*a*b^2*c^3 + 4*a*b*c^4 + 2*b^4*c^2 + 2*b^3*c^3 + 2*b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*c + 2*a^4*b^2 + 4*a^4*b*c + 2*a^4*c^2 + 2*a^3*b^3 - 3*a^3*b^2*c - 5*a^3*b*c^2 + 2*a^3*c^3 + 2*a^2*b^4 - 5*a^2*b^3*c - 12*a^2*b^2*c^2 - 3*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 4*a*b^4*c - 3*a*b^3*c^2 - 5*a*b^2*c^3 + 4*a*b*c^4 + 2*b^4*c^2 + 2*b^3*c^3 + 2*b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2) * (1 / (a^2 + a * b) + 1 / (b^2 + b * c) + 1 / (c^2 + c * a)) ≥ 9 / 2) := @solution
#print axioms solution
