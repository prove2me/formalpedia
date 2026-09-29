-- Prove2me | solution 1 for WorkbookSource.base_35771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:31.906427+00:00
-- url     : https://prove2.me/submissions/405e1b15-dd45-4fad-ab9f-4d06e2a5936a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a^2 + b^2 + c^2)^3 ≥ 27 * (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (8*a^6 + 24*a^4*b^2 - 27*a^4*b*c + 24*a^4*c^2 - 27*a^3*b^3 - 27*a^3*c^3 + 24*a^2*b^4 - 6*a^2*b^2*c^2 + 24*a^2*c^4 - 27*a*b^4*c - 27*a*b*c^4 + 8*b^6 + 24*b^4*c^2 - 27*b^3*c^3 + 24*b^2*c^4 + 8*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (126 : ℝ) * a^4 * (b - a)^2 + (126 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (126 : ℝ) * a^4 * (c - b)^2 + (314 : ℝ) * a^3 * (b - a)^3 + (471 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (537 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (190 : ℝ) * a^3 * (c - b)^3 + (327 : ℝ) * a^2 * (b - a)^4 + (654 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (894 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (567 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (141 : ℝ) * a^2 * (c - b)^4 + (168 : ℝ) * a^1 * (b - a)^5 + (420 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (666 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (579 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (261 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (48 : ℝ) * a^1 * (c - b)^5 + (37 : ℝ) * (b - a)^6 + (111 : ℝ) * (b - a)^5 * (c - b)^1 + (207 : ℝ) * (b - a)^4 * (c - b)^2 + (229 : ℝ) * (b - a)^3 * (c - b)^3 + (144 : ℝ) * (b - a)^2 * (c - b)^4 + (48 : ℝ) * (b - a)^1 * (c - b)^5 + (8 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (8*a^6 + 24*a^4*b^2 - 27*a^4*b*c + 24*a^4*c^2 - 27*a^3*b^3 - 27*a^3*c^3 + 24*a^2*b^4 - 6*a^2*b^2*c^2 + 24*a^2*c^4 - 27*a*b^4*c - 27*a*b*c^4 + 8*b^6 + 24*b^4*c^2 - 27*b^3*c^3 + 24*b^2*c^4 + 8*c^6) := by
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
  nlinarith only [hp]
example : (∀ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 8 * (a^2 + b^2 + c^2)^3 ≥ 27 * (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b)) := @solution
#print axioms solution
