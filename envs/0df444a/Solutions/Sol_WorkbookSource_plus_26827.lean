-- Prove2me | solution 1 for WorkbookSource.plus_26827
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:51:25.149057+00:00
-- url     : https://prove2.me/submissions/74ef3dc9-a73b-461d-affc-d2d468629573

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * a / (a + b) + 2 * b / (b + c) + 2 * c / (c + a)) ≤ (7 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a * b + b * c + c * a)) / (a + b + c) ^ 2   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^4*b + 5*a^4*c - a^3*b^2 + a^3*c^2 + a^2*b^3 - 8*a^2*b^2*c - 8*a^2*b*c^2 - a^2*c^3 + 5*a*b^4 - 8*a*b^2*c^2 + 3*a*c^4 + 3*b^4*c - b^3*c^2 + b^2*c^3 + 5*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^3 * (b - a)^2 + (32 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (32 : ℝ) * a^3 * (c - b)^2 + (64 : ℝ) * a^2 * (b - a)^3 + (105 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (105 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (32 : ℝ) * a^2 * (c - b)^3 + (40 : ℝ) * a^1 * (b - a)^4 + (92 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (106 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (54 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^1 * (c - b)^4 + (8 : ℝ) * (b - a)^5 + (24 : ℝ) * (b - a)^4 * (c - b)^1 + (32 : ℝ) * (b - a)^3 * (c - b)^2 + (21 : ℝ) * (b - a)^2 * (c - b)^3 + (5 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^4*b + 5*a^4*c - a^3*b^2 + a^3*c^2 + a^2*b^3 - 8*a^2*b^2*c - 8*a^2*b*c^2 - a^2*c^3 + 5*a*b^4 - 8*a*b^2*c^2 + 3*a*c^4 + 3*b^4*c - b^3*c^2 + b^2*c^3 + 5*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^3 * (c - a)^2 + (32 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (32 : ℝ) * a^3 * (b - c)^2 + (64 : ℝ) * a^2 * (c - a)^3 + (87 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (87 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (32 : ℝ) * a^2 * (b - c)^3 + (40 : ℝ) * a^1 * (c - a)^4 + (68 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (70 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (42 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (8 : ℝ) * a^1 * (b - c)^4 + (8 : ℝ) * (c - a)^5 + (16 : ℝ) * (c - a)^4 * (b - c)^1 + (16 : ℝ) * (c - a)^3 * (b - c)^2 + (11 : ℝ) * (c - a)^2 * (b - c)^3 + (3 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^4*b + 5*a^4*c - a^3*b^2 + a^3*c^2 + a^2*b^3 - 8*a^2*b^2*c - 8*a^2*b*c^2 - a^2*c^3 + 5*a*b^4 - 8*a*b^2*c^2 + 3*a*c^4 + 3*b^4*c - b^3*c^2 + b^2*c^3 + 5*b*c^4) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux0 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux1 a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux1 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux0 b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux1 c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have hn : 0 ≤ (3*a^4*b + 5*a^4*c - a^3*b^2 + a^3*c^2 + a^2*b^3 - 8*a^2*b^2*c - 8*a^2*b*c^2 - a^2*c^3 + 5*a*b^4 - 8*a*b^2*c^2 + 3*a*c^4 + 3*b^4*c - b^3*c^2 + b^2*c^3 + 5*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (2 * a / (a + b) + 2 * b / (b + c) + 2 * c / (c + a)) ≤ (7 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a * b + b * c + c * a)) / (a + b + c) ^ 2) := @solution
#print axioms solution
