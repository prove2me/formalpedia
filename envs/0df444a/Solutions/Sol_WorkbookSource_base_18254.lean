-- Prove2me | solution 1 for WorkbookSource.base_18254
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:34:37.433984+00:00
-- url     : https://prove2.me/submissions/cec2ff81-5c32-4c43-b625-1db0cb57220a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2) ≥ (7 / 25) * (1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (18*a^4*b^2 - 14*a^4*b*c + 18*a^4*c^2 + 36*a^3*b^3 - 20*a^3*b^2*c - 20*a^3*b*c^2 + 36*a^3*c^3 + 18*a^2*b^4 - 20*a^2*b^3*c - 54*a^2*b^2*c^2 - 20*a^2*b*c^3 + 18*a^2*c^4 - 14*a*b^4*c - 20*a*b^3*c^2 - 20*a*b^2*c^3 - 14*a*b*c^4 + 18*b^4*c^2 + 36*b^3*c^3 + 18*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (170 : ℝ) * a^4 * (b - a)^2 + (170 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (170 : ℝ) * a^4 * (c - b)^2 + (560 : ℝ) * a^3 * (b - a)^3 + (840 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (520 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (120 : ℝ) * a^3 * (c - b)^3 + (682 : ℝ) * a^2 * (b - a)^4 + (1364 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (906 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (224 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (22 : ℝ) * a^2 * (c - b)^4 + (364 : ℝ) * a^1 * (b - a)^5 + (910 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (772 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (248 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (22 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (72 : ℝ) * (b - a)^6 + (216 : ℝ) * (b - a)^5 * (c - b)^1 + (234 : ℝ) * (b - a)^4 * (c - b)^2 + (108 : ℝ) * (b - a)^3 * (c - b)^3 + (18 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (18*a^4*b^2 - 14*a^4*b*c + 18*a^4*c^2 + 36*a^3*b^3 - 20*a^3*b^2*c - 20*a^3*b*c^2 + 36*a^3*c^3 + 18*a^2*b^4 - 20*a^2*b^3*c - 54*a^2*b^2*c^2 - 20*a^2*b*c^3 + 18*a^2*c^4 - 14*a*b^4*c - 20*a*b^3*c^2 - 20*a*b^2*c^3 - 14*a*b*c^4 + 18*b^4*c^2 + 36*b^3*c^3 + 18*b^2*c^4) := by
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
  have hn : 0 ≤ (18*a^4*b^2 - 14*a^4*b*c + 18*a^4*c^2 + 36*a^3*b^3 - 20*a^3*b^2*c - 20*a^3*b*c^2 + 36*a^3*c^3 + 18*a^2*b^4 - 20*a^2*b^3*c - 54*a^2*b^2*c^2 - 20*a^2*b*c^3 + 18*a^2*c^4 - 14*a*b^4*c - 20*a*b^3*c^2 - 20*a*b^2*c^3 - 14*a*b*c^4 + 18*b^4*c^2 + 36*b^3*c^3 + 18*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0), (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / (a + b + c) ^ 2) ≥ (7 / 25) * (1 / a + 1 / b + 1 / c + 1 / (a + b + c)) ^ 2) := @solution
#print axioms solution
