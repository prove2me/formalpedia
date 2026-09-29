-- Prove2me | solution 1 for WorkbookSource.base_46828
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:11:30.35368+00:00
-- url     : https://prove2.me/submissions/c94eb0f7-ff01-4ee0-a7d8-6ba079c5f284

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + 3 * a * b * c) / (b + c)^2 + (b^3 + 3 * a * b * c) / (c + a)^2 + (c^3 + 3 * a * b * c) / (a + b)^2 ≥ a + b + c  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^7 + 2*a^6*b + 2*a^6*c + 5*a^5*b*c - 3*a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - 3*a^4*c^3 - 3*a^3*b^4 - 5*a^3*b^3*c + 3*a^3*b^2*c^2 - 5*a^3*b*c^3 - 3*a^3*c^4 - a^2*b^4*c + 3*a^2*b^3*c^2 + 3*a^2*b^2*c^3 - a^2*b*c^4 + 2*a*b^6 + 5*a*b^5*c - a*b^4*c^2 - 5*a*b^3*c^3 - a*b^2*c^4 + 5*a*b*c^5 + 2*a*c^6 + b^7 + 2*b^6*c - 3*b^4*c^3 - 3*b^3*c^4 + 2*b*c^6 + c^7) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (48 : ℝ) * a^5 * (b - a)^2 + (48 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (48 : ℝ) * a^5 * (c - b)^2 + (120 : ℝ) * a^4 * (b - a)^3 + (180 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (300 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (120 : ℝ) * a^4 * (c - b)^3 + (112 : ℝ) * a^3 * (b - a)^4 + (224 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (576 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (464 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (112 : ℝ) * a^3 * (c - b)^4 + (46 : ℝ) * a^2 * (b - a)^5 + (115 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (478 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (602 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (293 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (50 : ℝ) * a^2 * (c - b)^5 + (7 : ℝ) * a^1 * (b - a)^6 + (21 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (178 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (321 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (240 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (83 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (11 : ℝ) * a^1 * (c - b)^6 + (24 : ℝ) * (b - a)^5 * (c - b)^2 + (60 : ℝ) * (b - a)^4 * (c - b)^3 + (62 : ℝ) * (b - a)^3 * (c - b)^4 + (33 : ℝ) * (b - a)^2 * (c - b)^5 + (9 : ℝ) * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (c - b)^7 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^7 + 2*a^6*b + 2*a^6*c + 5*a^5*b*c - 3*a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - 3*a^4*c^3 - 3*a^3*b^4 - 5*a^3*b^3*c + 3*a^3*b^2*c^2 - 5*a^3*b*c^3 - 3*a^3*c^4 - a^2*b^4*c + 3*a^2*b^3*c^2 + 3*a^2*b^2*c^3 - a^2*b*c^4 + 2*a*b^6 + 5*a*b^5*c - a*b^4*c^2 - 5*a*b^3*c^3 - a*b^2*c^4 + 5*a*b*c^5 + 2*a*c^6 + b^7 + 2*b^6*c - 3*b^4*c^3 - 3*b^3*c^4 + 2*b*c^6 + c^7) := by
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
  have hn : 0 ≤ (a^7 + 2*a^6*b + 2*a^6*c + 5*a^5*b*c - 3*a^4*b^3 - a^4*b^2*c - a^4*b*c^2 - 3*a^4*c^3 - 3*a^3*b^4 - 5*a^3*b^3*c + 3*a^3*b^2*c^2 - 5*a^3*b*c^3 - 3*a^3*c^4 - a^2*b^4*c + 3*a^2*b^3*c^2 + 3*a^2*b^2*c^3 - a^2*b*c^4 + 2*a*b^6 + 5*a*b^5*c - a*b^4*c^2 - 5*a*b^3*c^3 - a*b^2*c^4 + 5*a*b*c^5 + 2*a*c^6 + b^7 + 2*b^6*c - 3*b^4*c^3 - 3*b^3*c^4 + 2*b*c^6 + c^7) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + 3 * a * b * c) / (b + c)^2 + (b^3 + 3 * a * b * c) / (c + a)^2 + (c^3 + 3 * a * b * c) / (a + b)^2 ≥ a + b + c) := @solution
#print axioms solution
