-- Prove2me | solution 1 for WorkbookSource.plus_80477
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:57:27.081863+00:00
-- url     : https://prove2.me/submissions/d3e09710-637e-404b-b231-ed8195743426

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 * (b + c) / (a^2 + b * c) + b^3 * (c + a) / (b^2 + a * c) + c^3 * (a + b) / (c^2 + a * b)) ≤ a^2 + b^2 + c^2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b*c + a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 + 2*a^4*b^2*c^2 - 2*a^4*c^4 + a^3*b^5 - a^3*b^3*c^2 - a^3*b^2*c^3 + a^3*c^5 - a^2*b^5*c + 2*a^2*b^4*c^2 - a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + a*b^6*c - a*b^5*c^2 - a*b^2*c^5 + a*b*c^6 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^6 * (b - a)^2 + (4 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^6 * (c - b)^2 + (12 : ℝ) * a^5 * (b - a)^3 + (18 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (30 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^5 * (c - b)^3 + (13 : ℝ) * a^4 * (b - a)^4 + (26 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (69 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (56 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (13 : ℝ) * a^4 * (c - b)^4 + (6 : ℝ) * a^3 * (b - a)^5 + (15 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (70 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (90 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (41 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (6 : ℝ) * a^3 * (c - b)^5 + (1 : ℝ) * a^2 * (b - a)^6 + (3 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (36 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (67 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (45 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (1 : ℝ) * a^2 * (c - b)^6 + (10 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (25 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (22 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (8 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (1 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (1 : ℝ) * (b - a)^6 * (c - b)^2 + (3 : ℝ) * (b - a)^5 * (c - b)^3 + (3 : ℝ) * (b - a)^4 * (c - b)^4 + (1 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b*c + a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 + 2*a^4*b^2*c^2 - 2*a^4*c^4 + a^3*b^5 - a^3*b^3*c^2 - a^3*b^2*c^3 + a^3*c^5 - a^2*b^5*c + 2*a^2*b^4*c^2 - a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + a*b^6*c - a*b^5*c^2 - a*b^2*c^5 + a*b*c^6 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5) := by
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
  have hn : 0 ≤ (a^6*b*c + a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 + 2*a^4*b^2*c^2 - 2*a^4*c^4 + a^3*b^5 - a^3*b^3*c^2 - a^3*b^2*c^3 + a^3*c^5 - a^2*b^5*c + 2*a^2*b^4*c^2 - a^2*b^3*c^3 + 2*a^2*b^2*c^4 - a^2*b*c^5 + a*b^6*c - a*b^5*c^2 - a*b^2*c^5 + a*b*c^6 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 * (b + c) / (a^2 + b * c) + b^3 * (c + a) / (b^2 + a * c) + c^3 * (a + b) / (c^2 + a * b)) ≤ a^2 + b^2 + c^2) := @solution
#print axioms solution
