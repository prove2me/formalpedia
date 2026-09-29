-- Prove2me | solution 1 for WorkbookSource.base_55716
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:31:14.221655+00:00
-- url     : https://prove2.me/submissions/9fe0de69-8b5b-4e8f-bcca-6b2de6e9c92d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 16 * b * c) / (b^2 + b * c + c^2) + (b^2 + 16 * c * a) / (c^2 + c * a + a^2) + (c^2 + 16 * a * b) / (a^2 + a * b + b^2) ≥ 22 / 3  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^6 + 3*a^5*b + 3*a^5*c - 19*a^4*b^2 + 29*a^4*b*c - 19*a^4*c^2 + 26*a^3*b^3 + 103*a^3*b^2*c + 103*a^3*b*c^2 + 26*a^3*c^3 - 19*a^2*b^4 + 103*a^2*b^3*c + 87*a^2*b^2*c^2 + 103*a^2*b*c^3 - 19*a^2*c^4 + 3*a*b^5 + 29*a*b^4*c + 103*a*b^3*c^2 + 103*a*b^2*c^3 + 29*a*b*c^4 + 3*a*c^5 + 3*b^6 + 3*b^5*c - 19*b^4*c^2 + 26*b^3*c^3 - 19*b^2*c^4 + 3*b*c^5 + 3*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (783 : ℝ) * a^6 + (3132 : ℝ) * a^5 * (b - a)^1 + (1566 : ℝ) * a^5 * (c - b)^1 + (4995 : ℝ) * a^4 * (b - a)^2 + (4995 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (1080 : ℝ) * a^4 * (c - b)^2 + (3978 : ℝ) * a^3 * (b - a)^3 + (5967 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2673 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (342 : ℝ) * a^3 * (c - b)^3 + (1605 : ℝ) * a^2 * (b - a)^4 + (3210 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2250 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (645 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (66 : ℝ) * a^2 * (c - b)^4 + (270 : ℝ) * a^1 * (b - a)^5 + (675 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (696 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (369 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (126 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (24 : ℝ) * a^1 * (c - b)^5 + (20 : ℝ) * (b - a)^4 * (c - b)^2 + (40 : ℝ) * (b - a)^3 * (c - b)^3 + (41 : ℝ) * (b - a)^2 * (c - b)^4 + (21 : ℝ) * (b - a)^1 * (c - b)^5 + (3 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^6 + 3*a^5*b + 3*a^5*c - 19*a^4*b^2 + 29*a^4*b*c - 19*a^4*c^2 + 26*a^3*b^3 + 103*a^3*b^2*c + 103*a^3*b*c^2 + 26*a^3*c^3 - 19*a^2*b^4 + 103*a^2*b^3*c + 87*a^2*b^2*c^2 + 103*a^2*b*c^3 - 19*a^2*c^4 + 3*a*b^5 + 29*a*b^4*c + 103*a*b^3*c^2 + 103*a*b^2*c^3 + 29*a*b*c^4 + 3*a*c^5 + 3*b^6 + 3*b^5*c - 19*b^4*c^2 + 26*b^3*c^3 - 19*b^2*c^4 + 3*b*c^5 + 3*c^6) := by
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
  have hn : 0 ≤ (3*a^6 + 3*a^5*b + 3*a^5*c - 19*a^4*b^2 + 29*a^4*b*c - 19*a^4*c^2 + 26*a^3*b^3 + 103*a^3*b^2*c + 103*a^3*b*c^2 + 26*a^3*c^3 - 19*a^2*b^4 + 103*a^2*b^3*c + 87*a^2*b^2*c^2 + 103*a^2*b*c^3 - 19*a^2*c^4 + 3*a*b^5 + 29*a*b^4*c + 103*a*b^3*c^2 + 103*a*b^2*c^3 + 29*a*b*c^4 + 3*a*c^5 + 3*b^6 + 3*b^5*c - 19*b^4*c^2 + 26*b^3*c^3 - 19*b^2*c^4 + 3*b*c^5 + 3*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + 16 * b * c) / (b^2 + b * c + c^2) + (b^2 + 16 * c * a) / (c^2 + c * a + a^2) + (c^2 + 16 * a * b) / (a^2 + a * b + b^2) ≥ 22 / 3) := @solution
#print axioms solution
