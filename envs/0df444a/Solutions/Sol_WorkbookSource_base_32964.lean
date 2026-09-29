-- Prove2me | solution 1 for WorkbookSource.base_32964
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:47:23.640895+00:00
-- url     : https://prove2.me/submissions/bd7af384-e76f-444d-bbb9-1202bcd9158b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2) / (c^2 + a * b) + (b^2 + c^2) / (a^2 + b * c) + (c^2 + a^2) / (b^2 + c * a) ≥ 3 + 4 * (a^2 + b^2 + c^2 - a * b - a * c - b * c) / (a + b + c)^2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7*b + a^7*c + 3*a^6*b^2 - 3*a^6*b*c + 3*a^6*c^2 - 4*a^5*b^3 + 5*a^5*b^2*c + 5*a^5*b*c^2 - 4*a^5*c^3 - a^4*b^3*c - 6*a^4*b^2*c^2 - a^4*b*c^3 - 4*a^3*b^5 - a^3*b^4*c + a^3*b^3*c^2 + a^3*b^2*c^3 - a^3*b*c^4 - 4*a^3*c^5 + 3*a^2*b^6 + 5*a^2*b^5*c - 6*a^2*b^4*c^2 + a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 5*a^2*b*c^5 + 3*a^2*c^6 + a*b^7 - 3*a*b^6*c + 5*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + 5*a*b^2*c^5 - 3*a*b*c^6 + a*c^7 + b^7*c + 3*b^6*c^2 - 4*b^5*c^3 - 4*b^3*c^5 + 3*b^2*c^6 + b*c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (40 : ℝ) * a^6 * (b - a)^2 + (40 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (40 : ℝ) * a^6 * (c - b)^2 + (130 : ℝ) * a^5 * (b - a)^3 + (195 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (285 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (110 : ℝ) * a^5 * (c - b)^3 + (167 : ℝ) * a^4 * (b - a)^4 + (334 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (676 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (509 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (117 : ℝ) * a^4 * (c - b)^4 + (106 : ℝ) * a^3 * (b - a)^5 + (265 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (742 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (848 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (389 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (62 : ℝ) * a^3 * (c - b)^5 + (33 : ℝ) * a^2 * (b - a)^6 + (99 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (421 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (677 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (466 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (144 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (17 : ℝ) * a^2 * (c - b)^6 + (4 : ℝ) * a^1 * (b - a)^7 + (14 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (124 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (275 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (254 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (113 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (24 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * a^1 * (c - b)^7 + (17 : ℝ) * (b - a)^6 * (c - b)^2 + (51 : ℝ) * (b - a)^5 * (c - b)^3 + (60 : ℝ) * (b - a)^4 * (c - b)^4 + (35 : ℝ) * (b - a)^3 * (c - b)^5 + (10 : ℝ) * (b - a)^2 * (c - b)^6 + (1 : ℝ) * (b - a)^1 * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7*b + a^7*c + 3*a^6*b^2 - 3*a^6*b*c + 3*a^6*c^2 - 4*a^5*b^3 + 5*a^5*b^2*c + 5*a^5*b*c^2 - 4*a^5*c^3 - a^4*b^3*c - 6*a^4*b^2*c^2 - a^4*b*c^3 - 4*a^3*b^5 - a^3*b^4*c + a^3*b^3*c^2 + a^3*b^2*c^3 - a^3*b*c^4 - 4*a^3*c^5 + 3*a^2*b^6 + 5*a^2*b^5*c - 6*a^2*b^4*c^2 + a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 5*a^2*b*c^5 + 3*a^2*c^6 + a*b^7 - 3*a*b^6*c + 5*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + 5*a*b^2*c^5 - 3*a*b*c^6 + a*c^7 + b^7*c + 3*b^6*c^2 - 4*b^5*c^3 - 4*b^3*c^5 + 3*b^2*c^6 + b*c^7) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux0 a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux0 b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (a^7*b + a^7*c + 3*a^6*b^2 - 3*a^6*b*c + 3*a^6*c^2 - 4*a^5*b^3 + 5*a^5*b^2*c + 5*a^5*b*c^2 - 4*a^5*c^3 - a^4*b^3*c - 6*a^4*b^2*c^2 - a^4*b*c^3 - 4*a^3*b^5 - a^3*b^4*c + a^3*b^3*c^2 + a^3*b^2*c^3 - a^3*b*c^4 - 4*a^3*c^5 + 3*a^2*b^6 + 5*a^2*b^5*c - 6*a^2*b^4*c^2 + a^2*b^3*c^3 - 6*a^2*b^2*c^4 + 5*a^2*b*c^5 + 3*a^2*c^6 + a*b^7 - 3*a*b^6*c + 5*a*b^5*c^2 - a*b^4*c^3 - a*b^3*c^4 + 5*a*b^2*c^5 - 3*a*b*c^6 + a*c^7 + b^7*c + 3*b^6*c^2 - 4*b^5*c^3 - 4*b^3*c^5 + 3*b^2*c^6 + b*c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2) / (c^2 + a * b) + (b^2 + c^2) / (a^2 + b * c) + (c^2 + a^2) / (b^2 + c * a) ≥ 3 + 4 * (a^2 + b^2 + c^2 - a * b - a * c - b * c) / (a + b + c)^2) := @solution
#print axioms solution
