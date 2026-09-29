-- Prove2me | solution 1 for WorkbookSource.base_10974
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:34:35.064251+00:00
-- url     : https://prove2.me/submissions/032a538c-7333-4e51-a4bf-1f7c7ef678f4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + b + 4 * c) + (b + c) / (b + c + 4 * a) + (c + a) / (c + a + 4 * b) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * (a * b + b * c + c * a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^5 + 16*a^4*b + 16*a^4*c - 20*a^3*b^2 + 64*a^3*b*c - 20*a^3*c^2 - 20*a^2*b^3 - 60*a^2*b^2*c - 60*a^2*b*c^2 - 20*a^2*c^3 + 16*a*b^4 + 64*a*b^3*c - 60*a*b^2*c^2 + 64*a*b*c^3 + 16*a*c^4 + 4*b^5 + 16*b^4*c - 20*b^3*c^2 - 20*b^2*c^3 + 16*b*c^4 + 4*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (144 : ℝ) * a^3 * (b - a)^2 + (144 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (144 : ℝ) * a^3 * (c - b)^2 + (240 : ℝ) * a^2 * (b - a)^3 + (360 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (504 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (192 : ℝ) * a^2 * (c - b)^3 + (100 : ℝ) * a^1 * (b - a)^4 + (200 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (396 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (296 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (52 : ℝ) * a^1 * (c - b)^4 + (56 : ℝ) * (b - a)^3 * (c - b)^2 + (84 : ℝ) * (b - a)^2 * (c - b)^3 + (36 : ℝ) * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^5 + 16*a^4*b + 16*a^4*c - 20*a^3*b^2 + 64*a^3*b*c - 20*a^3*c^2 - 20*a^2*b^3 - 60*a^2*b^2*c - 60*a^2*b*c^2 - 20*a^2*c^3 + 16*a*b^4 + 64*a*b^3*c - 60*a*b^2*c^2 + 64*a*b*c^3 + 16*a*c^4 + 4*b^5 + 16*b^4*c - 20*b^3*c^2 - 20*b^2*c^3 + 16*b*c^4 + 4*c^5) := by
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
  have hn : 0 ≤ (4*a^5 + 16*a^4*b + 16*a^4*c - 20*a^3*b^2 + 64*a^3*b*c - 20*a^3*c^2 - 20*a^2*b^3 - 60*a^2*b^2*c - 60*a^2*b*c^2 - 20*a^2*c^3 + 16*a*b^4 + 64*a*b^3*c - 60*a*b^2*c^2 + 64*a*b*c^3 + 16*a*c^4 + 4*b^5 + 16*b^4*c - 20*b^3*c^2 - 20*b^2*c^3 + 16*b*c^4 + 4*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (a + b + 4 * c) + (b + c) / (b + c + 4 * a) + (c + a) / (c + a + 4 * b) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * (a * b + b * c + c * a))) := @solution
#print axioms solution
