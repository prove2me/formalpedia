-- Prove2me | solution 1 for WorkbookSource.plus_9785
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:58:30.250413+00:00
-- url     : https://prove2.me/submissions/6e3729dc-9346-42d7-8698-fdb832b9f9aa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^2 + b^2 / c^2 + c^2 / a^2) + 2 ≥ 5 * (a^2 + b^2 + c^2) / (a * b + b * c + a * c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b*c^2 + a^5*c^3 - 5*a^4*b^2*c^2 + a^4*b*c^3 + a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + a^2*b^5*c - 5*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + a*b^3*c^4 + a*b^2*c^5 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * a^6 * (b - a)^2 + (7 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (7 : ℝ) * a^6 * (c - b)^2 + (32 : ℝ) * a^5 * (b - a)^3 + (60 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (48 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (10 : ℝ) * a^5 * (c - b)^3 + (61 : ℝ) * a^4 * (b - a)^4 + (162 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (158 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (57 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^4 * (c - b)^4 + (62 : ℝ) * a^3 * (b - a)^5 + (206 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (252 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (132 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (28 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^3 * (c - b)^5 + (35 : ℝ) * a^2 * (b - a)^6 + (136 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (201 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (138 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (43 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (5 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (10 : ℝ) * a^1 * (b - a)^7 + (44 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (76 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (64 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (26 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (4 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (1 : ℝ) * (b - a)^8 + (5 : ℝ) * (b - a)^7 * (c - b)^1 + (10 : ℝ) * (b - a)^6 * (c - b)^2 + (10 : ℝ) * (b - a)^5 * (c - b)^3 + (5 : ℝ) * (b - a)^4 * (c - b)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b*c^2 + a^5*c^3 - 5*a^4*b^2*c^2 + a^4*b*c^3 + a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + a^2*b^5*c - 5*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + a*b^3*c^4 + a*b^2*c^5 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (7 : ℝ) * a^6 * (c - a)^2 + (7 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (7 : ℝ) * a^6 * (b - c)^2 + (32 : ℝ) * a^5 * (c - a)^3 + (36 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (24 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (10 : ℝ) * a^5 * (b - c)^3 + (61 : ℝ) * a^4 * (c - a)^4 + (82 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (38 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (17 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (6 : ℝ) * a^4 * (b - c)^4 + (62 : ℝ) * a^3 * (c - a)^5 + (104 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (48 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (8 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (6 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^3 * (b - c)^5 + (35 : ℝ) * a^2 * (c - a)^6 + (74 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (46 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (6 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (1 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (10 : ℝ) * a^1 * (c - a)^7 + (26 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (22 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (6 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (1 : ℝ) * (c - a)^8 + (3 : ℝ) * (c - a)^7 * (b - c)^1 + (3 : ℝ) * (c - a)^6 * (b - c)^2 + (1 : ℝ) * (c - a)^5 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b*c^2 + a^5*c^3 - 5*a^4*b^2*c^2 + a^4*b*c^3 + a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + a^2*b^5*c - 5*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + a*b^3*c^4 + a*b^2*c^5 + b^3*c^5) := by
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
  have hn : 0 ≤ (a^5*b*c^2 + a^5*c^3 - 5*a^4*b^2*c^2 + a^4*b*c^3 + a^3*b^5 + a^3*b^4*c + 2*a^3*b^3*c^2 + 2*a^3*b^2*c^3 + a^2*b^5*c - 5*a^2*b^4*c^2 + 2*a^2*b^3*c^3 - 5*a^2*b^2*c^4 + a*b^3*c^4 + a*b^2*c^5 + b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / b^2 + b^2 / c^2 + c^2 / a^2) + 2 ≥ 5 * (a^2 + b^2 + c^2) / (a * b + b * c + a * c)) := @solution
#print axioms solution
