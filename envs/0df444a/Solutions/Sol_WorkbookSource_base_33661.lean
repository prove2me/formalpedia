-- Prove2me | solution 1 for WorkbookSource.base_33661
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:38:40.127945+00:00
-- url     : https://prove2.me/submissions/93a26c4f-9f12-4d46-84a9-d6b4311ad58b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2) : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) ≥ 27 / 13  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6/16 + 17*a^5*b/16 + 17*a^5*c/16 + 41*a^4*b^2/16 + 25*a^4*b*c/16 + 41*a^4*c^2/16 + 27*a^3*b^3/8 - 5*a^3*b^2*c/8 - 5*a^3*b*c^2/8 + 27*a^3*c^3/8 + 41*a^2*b^4/16 - 5*a^2*b^3*c/8 - 267*a^2*b^2*c^2/8 - 5*a^2*b*c^3/8 + 41*a^2*c^4/16 + 17*a*b^5/16 + 25*a*b^4*c/16 - 5*a*b^3*c^2/8 - 5*a*b^2*c^3/8 + 25*a*b*c^4/16 + 17*a*c^5/16 + 3*b^6/16 + 17*b^5*c/16 + 41*b^4*c^2/16 + 27*b^3*c^3/8 + 41*b^2*c^4/16 + 17*b*c^5/16 + 3*c^6/16) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (819/16 : ℝ) * a^4 * (b - a)^2 + (819/16 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (819/16 : ℝ) * a^4 * (c - b)^2 + (295/2 : ℝ) * a^3 * (b - a)^3 + (885/4 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (753/4 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (229/4 : ℝ) * a^3 * (c - b)^3 + (311/2 : ℝ) * a^2 * (b - a)^4 + (311 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2253/8 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1009/8 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (161/8 : ℝ) * a^2 * (c - b)^4 + (70 : ℝ) * a^1 * (b - a)^5 + (175 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (367/2 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (401/4 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (113/4 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (13/4 : ℝ) * a^1 * (c - b)^5 + (11 : ℝ) * (b - a)^6 + (33 : ℝ) * (b - a)^5 * (c - b)^1 + (83/2 : ℝ) * (b - a)^4 * (c - b)^2 + (28 : ℝ) * (b - a)^3 * (c - b)^3 + (171/16 : ℝ) * (b - a)^2 * (c - b)^4 + (35/16 : ℝ) * (b - a)^1 * (c - b)^5 + (3/16 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6/16 + 17*a^5*b/16 + 17*a^5*c/16 + 41*a^4*b^2/16 + 25*a^4*b*c/16 + 41*a^4*c^2/16 + 27*a^3*b^3/8 - 5*a^3*b^2*c/8 - 5*a^3*b*c^2/8 + 27*a^3*c^3/8 + 41*a^2*b^4/16 - 5*a^2*b^3*c/8 - 267*a^2*b^2*c^2/8 - 5*a^2*b*c^3/8 + 41*a^2*c^4/16 + 17*a*b^5/16 + 25*a*b^4*c/16 - 5*a*b^3*c^2/8 - 5*a*b^2*c^3/8 + 25*a*b*c^4/16 + 17*a*c^5/16 + 3*b^6/16 + 17*b^5*c/16 + 41*b^4*c^2/16 + 27*b^3*c^3/8 + 41*b^2*c^4/16 + 17*b*c^5/16 + 3*c^6/16) := by
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
  have he : (-27*a^2*b^2*c^2 - 14*a^2*b*c - 14*a*b^2*c - 14*a*b*c^2 - a*b - a*c - b*c + 12) = (3*a^6/16 + 17*a^5*b/16 + 17*a^5*c/16 + 41*a^4*b^2/16 + 25*a^4*b*c/16 + 41*a^4*c^2/16 + 27*a^3*b^3/8 - 5*a^3*b^2*c/8 - 5*a^3*b*c^2/8 + 27*a^3*c^3/8 + 41*a^2*b^4/16 - 5*a^2*b^3*c/8 - 267*a^2*b^2*c^2/8 - 5*a^2*b*c^3/8 + 41*a^2*c^4/16 + 17*a*b^5/16 + 25*a*b^4*c/16 - 5*a*b^3*c^2/8 - 5*a*b^2*c^3/8 + 25*a*b*c^4/16 + 17*a*c^5/16 + 3*b^6/16 + 17*b^5*c/16 + 41*b^4*c^2/16 + 27*b^3*c^3/8 + 41*b^2*c^4/16 + 17*b*c^5/16 + 3*c^6/16) := by
    linear_combination (-3*a^5/16 - 7*a^4*b/8 - 7*a^4*c/8 - 3*a^4/8 - 27*a^3*b^2/16 + 3*a^3*b*c/16 - 11*a^3*b/8 - 27*a^3*c^2/16 - 11*a^3*c/8 - 3*a^3/4 - 27*a^2*b^3/16 + 17*a^2*b^2*c/8 - 2*a^2*b^2 + 17*a^2*b*c^2/8 + 25*a^2*b*c/8 - 2*a^2*b - 27*a^2*c^3/16 - 2*a^2*c^2 - 2*a^2*c - 3*a^2/2 - 7*a*b^4/8 + 3*a*b^3*c/16 - 11*a*b^3/8 + 17*a*b^2*c^2/8 + 25*a*b^2*c/8 - 2*a*b^2 + 3*a*b*c^3/16 + 25*a*b*c^2/8 - 15*a*b*c/4 - 5*a*b/2 - 7*a*c^4/8 - 11*a*c^3/8 - 2*a*c^2 - 5*a*c/2 - 3*a - 3*b^5/16 - 7*b^4*c/8 - 3*b^4/8 - 27*b^3*c^2/16 - 11*b^3*c/8 - 3*b^3/4 - 27*b^2*c^3/16 - 2*b^2*c^2 - 2*b^2*c - 3*b^2/2 - 7*b*c^4/8 - 11*b*c^3/8 - 2*b*c^2 - 5*b*c/2 - 3*b - 3*c^5/16 - 3*c^4/8 - 3*c^3/4 - 3*c^2/2 - 3*c - 6) * hab
  have hn : 0 ≤ (-27*a^2*b^2*c^2 - 14*a^2*b*c - 14*a*b^2*c - 14*a*b*c^2 - a*b - a*c - b*c + 12) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2), 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) ≥ 27 / 13) := @solution
#print axioms solution
