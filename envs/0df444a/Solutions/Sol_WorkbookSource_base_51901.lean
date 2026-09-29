-- Prove2me | solution 1 for WorkbookSource.base_51901
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:14.869041+00:00
-- url     : https://prove2.me/submissions/449988da-1926-46ff-b7ff-b063953437ee

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a + 9 / 2) ≥ 5 * (b + c) / (b + c + 2 * a) + 5 * (c + a) / (c + a + 2 * b) + 5 * (a + b) / (a + b + 2 * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5*c + 4*a^4*b^2 - 8*a^4*b*c + 14*a^4*c^2 + 14*a^3*b^3 - 19*a^3*b^2*c - 11*a^3*b*c^2 + 14*a^3*c^3 + 14*a^2*b^4 - 11*a^2*b^3*c + 6*a^2*b^2*c^2 - 19*a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^5 - 8*a*b^4*c - 19*a*b^3*c^2 - 11*a*b^2*c^3 - 8*a*b*c^4 + 4*b^4*c^2 + 14*b^3*c^3 + 14*b^2*c^4 + 4*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (88 : ℝ) * a^4 * (b - a)^2 + (88 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (88 : ℝ) * a^4 * (c - b)^2 + (274 : ℝ) * a^3 * (b - a)^3 + (475 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (357 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (78 : ℝ) * a^3 * (c - b)^3 + (324 : ℝ) * a^2 * (b - a)^4 + (776 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (693 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (241 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (30 : ℝ) * a^2 * (c - b)^4 + (174 : ℝ) * a^1 * (b - a)^5 + (519 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (580 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (287 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (60 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (36 : ℝ) * (b - a)^6 + (126 : ℝ) * (b - a)^5 * (c - b)^1 + (170 : ℝ) * (b - a)^4 * (c - b)^2 + (110 : ℝ) * (b - a)^3 * (c - b)^3 + (34 : ℝ) * (b - a)^2 * (c - b)^4 + (4 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (4*a^5*c + 4*a^4*b^2 - 8*a^4*b*c + 14*a^4*c^2 + 14*a^3*b^3 - 19*a^3*b^2*c - 11*a^3*b*c^2 + 14*a^3*c^3 + 14*a^2*b^4 - 11*a^2*b^3*c + 6*a^2*b^2*c^2 - 19*a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^5 - 8*a*b^4*c - 19*a*b^3*c^2 - 11*a*b^2*c^3 - 8*a*b*c^4 + 4*b^4*c^2 + 14*b^3*c^3 + 14*b^2*c^4 + 4*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (88 : ℝ) * a^4 * (c - a)^2 + (88 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (88 : ℝ) * a^4 * (b - c)^2 + (274 : ℝ) * a^3 * (c - a)^3 + (347 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (229 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (78 : ℝ) * a^3 * (b - c)^3 + (324 : ℝ) * a^2 * (c - a)^4 + (520 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (309 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (113 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (30 : ℝ) * a^2 * (b - c)^4 + (174 : ℝ) * a^1 * (c - a)^5 + (351 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (244 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (79 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (20 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (4 : ℝ) * a^1 * (b - c)^5 + (36 : ℝ) * (c - a)^6 + (90 : ℝ) * (c - a)^5 * (b - c)^1 + (80 : ℝ) * (c - a)^4 * (b - c)^2 + (30 : ℝ) * (c - a)^3 * (b - c)^3 + (4 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5*c + 4*a^4*b^2 - 8*a^4*b*c + 14*a^4*c^2 + 14*a^3*b^3 - 19*a^3*b^2*c - 11*a^3*b*c^2 + 14*a^3*c^3 + 14*a^2*b^4 - 11*a^2*b^3*c + 6*a^2*b^2*c^2 - 19*a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^5 - 8*a*b^4*c - 19*a*b^3*c^2 - 11*a*b^2*c^3 - 8*a*b*c^4 + 4*b^4*c^2 + 14*b^3*c^3 + 14*b^2*c^4 + 4*b*c^5) := by
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
  have hn : 0 ≤ (4*a^5*c + 4*a^4*b^2 - 8*a^4*b*c + 14*a^4*c^2 + 14*a^3*b^3 - 19*a^3*b^2*c - 11*a^3*b*c^2 + 14*a^3*c^3 + 14*a^2*b^4 - 11*a^2*b^3*c + 6*a^2*b^2*c^2 - 19*a^2*b*c^3 + 4*a^2*c^4 + 4*a*b^5 - 8*a*b^4*c - 19*a*b^3*c^2 - 11*a*b^2*c^3 - 8*a*b*c^4 + 4*b^4*c^2 + 14*b^3*c^3 + 14*b^2*c^4 + 4*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / b + b / c + c / a + 9 / 2) ≥ 5 * (b + c) / (b + c + 2 * a) + 5 * (c + a) / (c + a + 2 * b) + 5 * (a + b) / (a + b + 2 * c)) := @solution
#print axioms solution
