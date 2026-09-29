-- Prove2me | solution 1 for WorkbookSource.base_46202
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:01:56.695294+00:00
-- url     : https://prove2.me/submissions/5b5942f8-6a86-45dd-b3ba-b0d805da3ef6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 3 * a * b * c + 2 * (a^2 * b^2 / (a + b) + b^2 * c^2 / (b + c) + c^2 * a^2 / (c + a)) ≥ 3 / 2 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*b + 2*a^5*c - a^4*b^2 - 2*a^4*b*c - a^4*c^2 - 2*a^3*b^3 - 2*a^3*c^3 - a^2*b^4 + 6*a^2*b^2*c^2 - a^2*c^4 + 2*a*b^5 - 2*a*b^4*c - 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c - b^4*c^2 - 2*b^3*c^3 - b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (8 : ℝ) * a^4 * (b - a)^2 + (8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^4 * (c - b)^2 + (12 : ℝ) * a^3 * (b - a)^3 + (18 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (46 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (20 : ℝ) * a^3 * (c - b)^3 + (4 : ℝ) * a^2 * (b - a)^4 + (8 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (66 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (62 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (16 : ℝ) * a^2 * (c - b)^4 + (36 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (54 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (26 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^1 * (c - b)^5 + (7 : ℝ) * (b - a)^4 * (c - b)^2 + (14 : ℝ) * (b - a)^3 * (c - b)^3 + (9 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*b + 2*a^5*c - a^4*b^2 - 2*a^4*b*c - a^4*c^2 - 2*a^3*b^3 - 2*a^3*c^3 - a^2*b^4 + 6*a^2*b^2*c^2 - a^2*c^4 + 2*a*b^5 - 2*a*b^4*c - 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c - b^4*c^2 - 2*b^3*c^3 - b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*b + 2*a^5*c - a^4*b^2 - 2*a^4*b*c - a^4*c^2 - 2*a^3*b^3 - 2*a^3*c^3 - a^2*b^4 + 6*a^2*b^2*c^2 - a^2*c^4 + 2*a*b^5 - 2*a*b^4*c - 2*a*b*c^4 + 2*a*c^5 + 2*b^5*c - b^4*c^2 - 2*b^3*c^3 - b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), a^3 + b^3 + c^3 + 3 * a * b * c + 2 * (a^2 * b^2 / (a + b) + b^2 * c^2 / (b + c) + c^2 * a^2 / (c + a)) ≥ 3 / 2 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))) := @solution
#print axioms solution
