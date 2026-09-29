-- Prove2me | solution 1 for WorkbookSource.base_21613
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:49:13.208306+00:00
-- url     : https://prove2.me/submissions/11798240-e499-45ba-8588-0674c06c0f36

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * (a + b + c) ^ 2) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a + b) * (a + c) / (a ^ 2 + b * c) + (b + c) * (b + a) / (b ^ 2 + c * a) + (c + a) * (c + b) / (c ^ 2 + a * b)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b^2 + a^6*b*c + a^6*c^2 + a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 - 2*a^4*c^4 + a^3*b^5 - a^3*b^3*c^2 - a^3*b^2*c^3 + a^3*c^5 + a^2*b^6 - a^2*b^5*c - a^2*b^3*c^3 - a^2*b*c^5 + a^2*c^6 + a*b^6*c - a*b^5*c^2 - a*b^2*c^5 + a*b*c^6 + b^6*c^2 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^6 * (b - a)^2 + (20 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (20 : ℝ) * a^6 * (c - b)^2 + (76 : ℝ) * a^5 * (b - a)^3 + (114 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (126 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (44 : ℝ) * a^5 * (c - b)^3 + (121 : ℝ) * a^4 * (b - a)^4 + (242 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (313 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (192 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (41 : ℝ) * a^4 * (c - b)^4 + (106 : ℝ) * a^3 * (b - a)^5 + (265 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (394 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (326 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (127 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (18 : ℝ) * a^3 * (c - b)^5 + (55 : ℝ) * a^2 * (b - a)^6 + (165 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (277 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (279 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (148 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (36 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (3 : ℝ) * a^2 * (c - b)^6 + (16 : ℝ) * a^1 * (b - a)^7 + (56 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (106 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (125 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (82 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (26 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (3 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (2 : ℝ) * (b - a)^8 + (8 : ℝ) * (b - a)^7 * (c - b)^1 + (17 : ℝ) * (b - a)^6 * (c - b)^2 + (23 : ℝ) * (b - a)^5 * (c - b)^3 + (18 : ℝ) * (b - a)^4 * (c - b)^4 + (7 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b^2 + a^6*b*c + a^6*c^2 + a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 - 2*a^4*c^4 + a^3*b^5 - a^3*b^3*c^2 - a^3*b^2*c^3 + a^3*c^5 + a^2*b^6 - a^2*b^5*c - a^2*b^3*c^3 - a^2*b*c^5 + a^2*c^6 + a*b^6*c - a*b^5*c^2 - a*b^2*c^5 + a*b*c^6 + b^6*c^2 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*b^2 + a^6*b*c + a^6*c^2 + a^5*b^3 - a^5*b^2*c - a^5*b*c^2 + a^5*c^3 - 2*a^4*b^4 - 2*a^4*c^4 + a^3*b^5 - a^3*b^3*c^2 - a^3*b^2*c^3 + a^3*c^5 + a^2*b^6 - a^2*b^5*c - a^2*b^3*c^3 - a^2*b*c^5 + a^2*c^6 + a*b^6*c - a*b^5*c^2 - a*b^2*c^5 + a*b*c^6 + b^6*c^2 + b^5*c^3 - 2*b^4*c^4 + b^3*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * (a + b + c) ^ 2) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a + b) * (a + c) / (a ^ 2 + b * c) + (b + c) * (b + a) / (b ^ 2 + c * a) + (c + a) * (c + b) / (c ^ 2 + a * b)) := @solution
#print axioms solution
