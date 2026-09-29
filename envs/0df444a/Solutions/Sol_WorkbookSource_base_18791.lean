-- Prove2me | solution 1 for WorkbookSource.base_18791
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:37:19.179519+00:00
-- url     : https://prove2.me/submissions/d9bc76aa-f119-4046-a5f2-a564f8a5650b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (c + a) * (c + b) / (a ^ 2 + b ^ 2 + a * b) + (a + c) * (a + b) / (b ^ 2 + c ^ 2 + b * c) + (b + a) * (b + c) / (c ^ 2 + a ^ 2 + a * c) ≥ 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - 2*a^4*b^2 - 2*a^4*c^2 - a^3*b^3 - a^3*c^3 - 2*a^2*b^4 - 2*a^2*c^4 + 2*a*b^5 + 2*a*c^5 + b^6 + 2*b^5*c - 2*b^4*c^2 - b^3*c^3 - 2*b^2*c^4 + 2*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (21 : ℝ) * a^4 * (b - a)^2 + (21 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (21 : ℝ) * a^4 * (c - b)^2 + (42 : ℝ) * a^3 * (b - a)^3 + (63 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (105 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (42 : ℝ) * a^3 * (c - b)^3 + (31 : ℝ) * a^2 * (b - a)^4 + (62 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (156 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (125 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (31 : ℝ) * a^2 * (c - b)^4 + (10 : ℝ) * a^1 * (b - a)^5 + (25 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (92 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (113 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (56 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^1 * (c - b)^5 + (1 : ℝ) * (b - a)^6 + (3 : ℝ) * (b - a)^5 * (c - b)^1 + (18 : ℝ) * (b - a)^4 * (c - b)^2 + (31 : ℝ) * (b - a)^3 * (c - b)^3 + (23 : ℝ) * (b - a)^2 * (c - b)^4 + (8 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - 2*a^4*b^2 - 2*a^4*c^2 - a^3*b^3 - a^3*c^3 - 2*a^2*b^4 - 2*a^2*c^4 + 2*a*b^5 + 2*a*c^5 + b^6 + 2*b^5*c - 2*b^4*c^2 - b^3*c^3 - 2*b^2*c^4 + 2*b*c^5 + c^6) := by
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
  have hn : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - 2*a^4*b^2 - 2*a^4*c^2 - a^3*b^3 - a^3*c^3 - 2*a^2*b^4 - 2*a^2*c^4 + 2*a*b^5 + 2*a*c^5 + b^6 + 2*b^5*c - 2*b^4*c^2 - b^3*c^3 - 2*b^2*c^4 + 2*b*c^5 + c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (c + a) * (c + b) / (a ^ 2 + b ^ 2 + a * b) + (a + c) * (a + b) / (b ^ 2 + c ^ 2 + b * c) + (b + a) * (b + c) / (c ^ 2 + a ^ 2 + a * c) ≥ 4) := @solution
#print axioms solution
