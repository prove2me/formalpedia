-- Prove2me | solution 1 for WorkbookSource.plus_56732
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:45:08.816774+00:00
-- url     : https://prove2.me/submissions/4f2b4925-eec5-4835-8cdb-96cb164107ed

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≤ (a + b + c) ^ 2 / (a * b + b * c + c * a) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6*b*c + 2*a^5*b^3 - 2*a^5*b^2*c - 2*a^5*b*c^2 + 2*a^5*c^3 + 4*a^4*b^4 - 3*a^4*b^3*c - 5*a^4*b^2*c^2 - 3*a^4*b*c^3 + 4*a^4*c^4 + 2*a^3*b^5 - 3*a^3*b^4*c + 5*a^3*b^3*c^2 + 5*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^3*c^5 - 2*a^2*b^5*c - 5*a^2*b^4*c^2 + 5*a^2*b^3*c^3 - 5*a^2*b^2*c^4 - 2*a^2*b*c^5 + 2*a*b^6*c - 2*a*b^5*c^2 - 3*a*b^4*c^3 - 3*a*b^3*c^4 - 2*a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 + 4*b^4*c^4 + 2*b^3*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (27 : ℝ) * a^6 * (b - a)^2 + (27 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (27 : ℝ) * a^6 * (c - b)^2 + (126 : ℝ) * a^5 * (b - a)^3 + (189 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (135 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (36 : ℝ) * a^5 * (c - b)^3 + (252 : ℝ) * a^4 * (b - a)^4 + (504 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (396 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (144 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (27 : ℝ) * a^4 * (c - b)^4 + (276 : ℝ) * a^3 * (b - a)^5 + (690 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (672 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (318 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (84 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^3 * (c - b)^5 + (173 : ℝ) * a^2 * (b - a)^6 + (519 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (615 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (365 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (120 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (24 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (2 : ℝ) * a^2 * (c - b)^6 + (58 : ℝ) * a^1 * (b - a)^7 + (203 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (281 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (195 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (73 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (16 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (8 : ℝ) * (b - a)^8 + (32 : ℝ) * (b - a)^7 * (c - b)^1 + (50 : ℝ) * (b - a)^6 * (c - b)^2 + (38 : ℝ) * (b - a)^5 * (c - b)^3 + (14 : ℝ) * (b - a)^4 * (c - b)^4 + (2 : ℝ) * (b - a)^3 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6*b*c + 2*a^5*b^3 - 2*a^5*b^2*c - 2*a^5*b*c^2 + 2*a^5*c^3 + 4*a^4*b^4 - 3*a^4*b^3*c - 5*a^4*b^2*c^2 - 3*a^4*b*c^3 + 4*a^4*c^4 + 2*a^3*b^5 - 3*a^3*b^4*c + 5*a^3*b^3*c^2 + 5*a^3*b^2*c^3 - 3*a^3*b*c^4 + 2*a^3*c^5 - 2*a^2*b^5*c - 5*a^2*b^4*c^2 + 5*a^2*b^3*c^3 - 5*a^2*b^2*c^4 - 2*a^2*b*c^5 + 2*a*b^6*c - 2*a*b^5*c^2 - 3*a*b^4*c^3 - 3*a*b^3*c^4 - 2*a*b^2*c^5 + 2*a*b*c^6 + 2*b^5*c^3 + 4*b^4*c^4 + 2*b^3*c^5) := by
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
  have hn : 0 ≤ ((a + b + c)*(2*a^5*b*c + 2*a^4*b^3 - 4*a^4*b^2*c - 4*a^4*b*c^2 + 2*a^4*c^3 + 2*a^3*b^4 - a^3*b^3*c + 3*a^3*b^2*c^2 - a^3*b*c^3 + 2*a^3*c^4 - 4*a^2*b^4*c + 3*a^2*b^3*c^2 + 3*a^2*b^2*c^3 - 4*a^2*b*c^4 + 2*a*b^5*c - 4*a*b^4*c^2 - a*b^3*c^3 - 4*a*b^2*c^4 + 2*a*b*c^5 + 2*b^4*c^3 + 2*b^3*c^4)) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≤ (a + b + c) ^ 2 / (a * b + b * c + c * a) ^ 2) := @solution
#print axioms solution
