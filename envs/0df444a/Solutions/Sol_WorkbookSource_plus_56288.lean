-- Prove2me | solution 1 for WorkbookSource.plus_56288
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:42:12.476217+00:00
-- url     : https://prove2.me/submissions/6589409c-ee72-4b42-bc8d-23e32cc05117

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b / c ^ 3 + b * c / a ^ 3 + c * a / b ^ 3 ≥ 1 / a + 1 / b + 1 / c   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^4 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - a^2*b^3*c^3 + b^4*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (5 : ℝ) * a^6 * (b - a)^2 + (5 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (5 : ℝ) * a^6 * (c - b)^2 + (24 : ℝ) * a^5 * (b - a)^3 + (36 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (24 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (6 : ℝ) * a^5 * (c - b)^3 + (47 : ℝ) * a^4 * (b - a)^4 + (94 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (66 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (19 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (2 : ℝ) * a^4 * (c - b)^4 + (48 : ℝ) * a^3 * (b - a)^5 + (120 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (104 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (36 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (4 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (27 : ℝ) * a^2 * (b - a)^6 + (81 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (87 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (39 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (6 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (8 : ℝ) * a^1 * (b - a)^7 + (28 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (36 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (20 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (4 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (1 : ℝ) * (b - a)^8 + (4 : ℝ) * (b - a)^7 * (c - b)^1 + (6 : ℝ) * (b - a)^6 * (c - b)^2 + (4 : ℝ) * (b - a)^5 * (c - b)^3 + (1 : ℝ) * (b - a)^4 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^4 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - a^2*b^3*c^3 + b^4*c^4) := by
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
  have hn : 0 ≤ (a^4*b^4 + a^4*c^4 - a^3*b^3*c^2 - a^3*b^2*c^3 - a^2*b^3*c^3 + b^4*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a * b / c ^ 3 + b * c / a ^ 3 + c * a / b ^ 3 ≥ 1 / a + 1 / b + 1 / c) := @solution
#print axioms solution
