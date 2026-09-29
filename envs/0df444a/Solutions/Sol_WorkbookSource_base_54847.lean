-- Prove2me | solution 1 for WorkbookSource.base_54847
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:23:01.201356+00:00
-- url     : https://prove2.me/submissions/78d67d67-5241-455c-998a-390a0d30b42e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (6 * a ^ 2 + b * c) + 1 / (6 * b ^ 2 + c * a) + 1 / (6 * c ^ 2 + a * b)) ≥ 9 / 7 * 1 / (a * b + b * c + c * a)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (42*a^4*b^2 + 30*a^4*b*c + 42*a^4*c^2 - 72*a^3*b^3 + 301*a^3*b^2*c + 301*a^3*b*c^2 - 72*a^3*c^3 + 42*a^2*b^4 + 301*a^2*b^3*c - 1932*a^2*b^2*c^2 + 301*a^2*b*c^3 + 42*a^2*c^4 + 30*a*b^4*c + 301*a*b^3*c^2 + 301*a*b^2*c^3 + 30*a*b*c^4 + 42*b^4*c^2 - 72*b^3*c^3 + 42*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (812 : ℝ) * a^4 * (b - a)^2 + (812 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (812 : ℝ) * a^4 * (c - b)^2 + (2334 : ℝ) * a^3 * (b - a)^3 + (3501 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (2995 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (914 : ℝ) * a^3 * (c - b)^3 + (2244 : ℝ) * a^2 * (b - a)^4 + (4488 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (3843 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (1599 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (114 : ℝ) * a^2 * (c - b)^4 + (734 : ℝ) * a^1 * (b - a)^5 + (1835 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1696 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (709 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (114 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * (b - a)^6 + (36 : ℝ) * (b - a)^5 * (c - b)^1 + (78 : ℝ) * (b - a)^4 * (c - b)^2 + (96 : ℝ) * (b - a)^3 * (c - b)^3 + (42 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (42*a^4*b^2 + 30*a^4*b*c + 42*a^4*c^2 - 72*a^3*b^3 + 301*a^3*b^2*c + 301*a^3*b*c^2 - 72*a^3*c^3 + 42*a^2*b^4 + 301*a^2*b^3*c - 1932*a^2*b^2*c^2 + 301*a^2*b*c^3 + 42*a^2*c^4 + 30*a*b^4*c + 301*a*b^3*c^2 + 301*a*b^2*c^3 + 30*a*b*c^4 + 42*b^4*c^2 - 72*b^3*c^3 + 42*b^2*c^4) := by
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
  have hn : 0 ≤ (42*a^4*b^2 + 30*a^4*b*c + 42*a^4*c^2 - 72*a^3*b^3 + 301*a^3*b^2*c + 301*a^3*b*c^2 - 72*a^3*c^3 + 42*a^2*b^4 + 301*a^2*b^3*c - 1932*a^2*b^2*c^2 + 301*a^2*b*c^3 + 42*a^2*c^4 + 30*a*b^4*c + 301*a*b^3*c^2 + 301*a*b^2*c^3 + 30*a*b*c^4 + 42*b^4*c^2 - 72*b^3*c^3 + 42*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (6 * a ^ 2 + b * c) + 1 / (6 * b ^ 2 + c * a) + 1 / (6 * c ^ 2 + a * b)) ≥ 9 / 7 * 1 / (a * b + b * c + c * a)) := @solution
#print axioms solution
