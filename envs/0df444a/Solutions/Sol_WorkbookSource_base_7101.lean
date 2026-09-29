-- Prove2me | solution 1 for WorkbookSource.base_7101
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:27:01.454122+00:00
-- url     : https://prove2.me/submissions/d76d4783-b442-4d03-9369-9cabdec7e478

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a + b + c)) * (1 / (a + b) + 1 / (b + c) + 1 / (a + c)) ≥ 1 / (a * b + b * c + c * a) + 1 / (2 * (a ^ 2 + b ^ 2 + c ^ 2))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 + 4*a^4*b*c + a^4*c^2 - 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + 4*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 4*a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (12 : ℝ) * a^4 * (b - a)^2 + (12 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (12 : ℝ) * a^4 * (c - b)^2 + (30 : ℝ) * a^3 * (b - a)^3 + (45 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (51 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (18 : ℝ) * a^3 * (c - b)^3 + (24 : ℝ) * a^2 * (b - a)^4 + (48 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (63 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (39 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^5 + (15 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (24 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (21 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (1 : ℝ) * (b - a)^4 * (c - b)^2 + (2 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 + 4*a^4*b*c + a^4*c^2 - 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + 4*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 4*a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4) := by
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
  have hn : 0 ≤ (a^4*b^2 + 4*a^4*b*c + a^4*c^2 - 2*a^3*b^3 - a^3*b^2*c - a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 - a^2*b^3*c - 6*a^2*b^2*c^2 - a^2*b*c^3 + a^2*c^4 + 4*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 4*a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (a + b + c)) * (1 / (a + b) + 1 / (b + c) + 1 / (a + c)) ≥ 1 / (a * b + b * c + c * a) + 1 / (2 * (a ^ 2 + b ^ 2 + c ^ 2))) := @solution
#print axioms solution
