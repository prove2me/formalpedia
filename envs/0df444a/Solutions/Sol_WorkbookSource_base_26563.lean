-- Prove2me | solution 1 for WorkbookSource.base_26563
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:30:11.421787+00:00
-- url     : https://prove2.me/submissions/06e92c82-01d4-45bc-bc72-140ddaea10a5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * ((a^2 + b^2 + c^2) / (a * b + b * c + c * a)) ≥ (a^2 / (c^2 + c * a + a * b)) + (b^2 / (a^2 + a * b + b * c)) + (c^2 / (b^2 + b * c + c * a)) + 1  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b*c + a^6*c^2 + a^5*b^3 + 2*a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - a^4*b^3*c - 3*a^4*b^2*c^2 + a^4*b*c^3 + a^3*b^5 + a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 + a^3*c^5 + a^2*b^6 - a^2*b^5*c - 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 - 3*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - a*b^4*c^3 + a*b^3*c^4 - a*b^2*c^5 + a*b*c^6 + b^5*c^3 + b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (30 : ℝ) * a^6 * (b - a)^2 + (30 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (30 : ℝ) * a^6 * (c - b)^2 + (124 : ℝ) * a^5 * (b - a)^3 + (192 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (180 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (56 : ℝ) * a^5 * (c - b)^3 + (212 : ℝ) * a^4 * (b - a)^4 + (444 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (466 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (234 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (42 : ℝ) * a^4 * (c - b)^4 + (193 : ℝ) * a^3 * (b - a)^5 + (512 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (628 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (410 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (131 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (15 : ℝ) * a^3 * (c - b)^5 + (99 : ℝ) * a^2 * (b - a)^6 + (321 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (463 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (368 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (160 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (33 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^2 * (c - b)^6 + (27 : ℝ) * a^1 * (b - a)^7 + (105 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (178 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (168 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (91 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (26 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (3 : ℝ) * (b - a)^8 + (14 : ℝ) * (b - a)^7 * (c - b)^1 + (28 : ℝ) * (b - a)^6 * (c - b)^2 + (31 : ℝ) * (b - a)^5 * (c - b)^3 + (20 : ℝ) * (b - a)^4 * (c - b)^4 + (7 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^6*b*c + a^6*c^2 + a^5*b^3 + 2*a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - a^4*b^3*c - 3*a^4*b^2*c^2 + a^4*b*c^3 + a^3*b^5 + a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 + a^3*c^5 + a^2*b^6 - a^2*b^5*c - 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 - 3*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - a*b^4*c^3 + a*b^3*c^4 - a*b^2*c^5 + a*b*c^6 + b^5*c^3 + b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (30 : ℝ) * a^6 * (c - a)^2 + (30 : ℝ) * a^6 * (c - a)^1 * (b - c)^1 + (30 : ℝ) * a^6 * (b - c)^2 + (124 : ℝ) * a^5 * (c - a)^3 + (180 : ℝ) * a^5 * (c - a)^2 * (b - c)^1 + (168 : ℝ) * a^5 * (c - a)^1 * (b - c)^2 + (56 : ℝ) * a^5 * (b - c)^3 + (212 : ℝ) * a^4 * (c - a)^4 + (404 : ℝ) * a^4 * (c - a)^3 * (b - c)^1 + (406 : ℝ) * a^4 * (c - a)^2 * (b - c)^2 + (214 : ℝ) * a^4 * (c - a)^1 * (b - c)^3 + (42 : ℝ) * a^4 * (b - c)^4 + (193 : ℝ) * a^3 * (c - a)^5 + (453 : ℝ) * a^3 * (c - a)^4 * (b - c)^1 + (510 : ℝ) * a^3 * (c - a)^3 * (b - c)^2 + (332 : ℝ) * a^3 * (c - a)^2 * (b - c)^3 + (112 : ℝ) * a^3 * (c - a)^1 * (b - c)^4 + (15 : ℝ) * a^3 * (b - c)^5 + (99 : ℝ) * a^2 * (c - a)^6 + (273 : ℝ) * a^2 * (c - a)^5 * (b - c)^1 + (343 : ℝ) * a^2 * (c - a)^4 * (b - c)^2 + (254 : ℝ) * a^2 * (c - a)^3 * (b - c)^3 + (109 : ℝ) * a^2 * (c - a)^2 * (b - c)^4 + (24 : ℝ) * a^2 * (c - a)^1 * (b - c)^5 + (2 : ℝ) * a^2 * (b - c)^6 + (27 : ℝ) * a^1 * (c - a)^7 + (84 : ℝ) * a^1 * (c - a)^6 * (b - c)^1 + (115 : ℝ) * a^1 * (c - a)^5 * (b - c)^2 + (92 : ℝ) * a^1 * (c - a)^4 * (b - c)^3 + (44 : ℝ) * a^1 * (c - a)^3 * (b - c)^4 + (11 : ℝ) * a^1 * (c - a)^2 * (b - c)^5 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^6 + (3 : ℝ) * (c - a)^8 + (10 : ℝ) * (c - a)^7 * (b - c)^1 + (14 : ℝ) * (c - a)^6 * (b - c)^2 + (11 : ℝ) * (c - a)^5 * (b - c)^3 + (5 : ℝ) * (c - a)^4 * (b - c)^4 + (1 : ℝ) * (c - a)^3 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b*c + a^6*c^2 + a^5*b^3 + 2*a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - a^4*b^3*c - 3*a^4*b^2*c^2 + a^4*b*c^3 + a^3*b^5 + a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 + a^3*c^5 + a^2*b^6 - a^2*b^5*c - 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 - 3*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - a*b^4*c^3 + a*b^3*c^4 - a*b^2*c^5 + a*b*c^6 + b^5*c^3 + b^3*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*b*c + a^6*c^2 + a^5*b^3 + 2*a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - a^4*b^3*c - 3*a^4*b^2*c^2 + a^4*b*c^3 + a^3*b^5 + a^3*b^4*c - 2*a^3*b^3*c^2 - 2*a^3*b^2*c^3 - a^3*b*c^4 + a^3*c^5 + a^2*b^6 - a^2*b^5*c - 3*a^2*b^4*c^2 - 2*a^2*b^3*c^3 - 3*a^2*b^2*c^4 + 2*a^2*b*c^5 + a*b^6*c + 2*a*b^5*c^2 - a*b^4*c^3 + a*b^3*c^4 - a*b^2*c^5 + a*b*c^6 + b^5*c^3 + b^3*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 2 * ((a^2 + b^2 + c^2) / (a * b + b * c + c * a)) ≥ (a^2 / (c^2 + c * a + a * b)) + (b^2 / (a^2 + a * b + b * c)) + (c^2 / (b^2 + b * c + c * a)) + 1) := @solution
#print axioms solution
