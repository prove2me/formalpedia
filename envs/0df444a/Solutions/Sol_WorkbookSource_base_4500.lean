-- Prove2me | solution 1 for WorkbookSource.base_4500
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:24.235419+00:00
-- url     : https://prove2.me/submissions/878bcb94-0de4-4a13-8214-c2da6f843f24

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3 + 3 * a * b * c) / (a + b) / (b + c) / (c + a) + (a + b + c)^2 / 6 / (a^2 + b^2 + c^2) ≥ 5 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (12*a^5 - 13*a^4*b - 13*a^4*c + 3*a^3*b^2 + 18*a^3*b*c + 3*a^3*c^2 + 3*a^2*b^3 - 10*a^2*b^2*c - 10*a^2*b*c^2 + 3*a^2*c^3 - 13*a*b^4 + 18*a*b^3*c - 10*a*b^2*c^2 + 18*a*b*c^3 - 13*a*c^4 + 12*b^5 - 13*b^4*c + 3*b^3*c^2 + 3*b^2*c^3 - 13*b*c^4 + 12*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (22 : ℝ) * a^3 * (b - a)^2 + (22 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (22 : ℝ) * a^3 * (c - b)^2 + (26 : ℝ) * a^2 * (b - a)^3 + (39 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (93 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (40 : ℝ) * a^2 * (c - b)^3 + (20 : ℝ) * a^1 * (b - a)^4 + (40 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (128 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (108 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (34 : ℝ) * a^1 * (c - b)^4 + (4 : ℝ) * (b - a)^5 + (10 : ℝ) * (b - a)^4 * (c - b)^1 + (54 : ℝ) * (b - a)^3 * (c - b)^2 + (71 : ℝ) * (b - a)^2 * (c - b)^3 + (47 : ℝ) * (b - a)^1 * (c - b)^4 + (12 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (12*a^5 - 13*a^4*b - 13*a^4*c + 3*a^3*b^2 + 18*a^3*b*c + 3*a^3*c^2 + 3*a^2*b^3 - 10*a^2*b^2*c - 10*a^2*b*c^2 + 3*a^2*c^3 - 13*a*b^4 + 18*a*b^3*c - 10*a*b^2*c^2 + 18*a*b*c^3 - 13*a*c^4 + 12*b^5 - 13*b^4*c + 3*b^3*c^2 + 3*b^2*c^3 - 13*b*c^4 + 12*c^5) := by
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
  have hn : 0 ≤ (12*a^5 - 13*a^4*b - 13*a^4*c + 3*a^3*b^2 + 18*a^3*b*c + 3*a^3*c^2 + 3*a^2*b^3 - 10*a^2*b^2*c - 10*a^2*b*c^2 + 3*a^2*c^3 - 13*a*b^4 + 18*a*b^3*c - 10*a*b^2*c^2 + 18*a*b*c^3 - 13*a*c^4 + 12*b^5 - 13*b^4*c + 3*b^3*c^2 + 3*b^2*c^3 - 13*b*c^4 + 12*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 + b^3 + c^3 + 3 * a * b * c) / (a + b) / (b + c) / (c + a) + (a + b + c)^2 / 6 / (a^2 + b^2 + c^2) ≥ 5 / 4) := @solution
#print axioms solution
