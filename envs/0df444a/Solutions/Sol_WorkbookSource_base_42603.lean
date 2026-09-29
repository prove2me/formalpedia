-- Prove2me | solution 1 for WorkbookSource.base_42603
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:33:15.167909+00:00
-- url     : https://prove2.me/submissions/61bee3d5-b0f2-4cd8-87d4-dc219344d522

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1)) ≥ (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^3*b^2 + 4*a^3*b + 4*a^3*c^2 + 4*a^3*c + 2*a^3 + 4*a^2*b^3 - 8*a^2*b^2*c + 8*a^2*b^2 - 8*a^2*b*c^2 - 16*a^2*b*c + 3*a^2*b + 4*a^2*c^3 + 8*a^2*c^2 + 3*a^2*c + 2*a^2 + 4*a*b^3 - 8*a*b^2*c^2 - 16*a*b^2*c + 3*a*b^2 - 16*a*b*c^2 - 24*a*b*c - 2*a*b + 4*a*c^3 + 3*a*c^2 - 2*a*c + 4*b^3*c^2 + 4*b^3*c + 2*b^3 + 4*b^2*c^3 + 8*b^2*c^2 + 3*b^2*c + 2*b^2 + 4*b*c^3 + 3*b*c^2 - 2*b*c + 2*c^3 + 2*c^2) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (16 : ℝ) * a^3 * (b - a)^2 + (16 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (16 : ℝ) * a^3 * (c - b)^2 + (40 : ℝ) * a^2 * (b - a)^3 + (60 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (24 : ℝ) * a^2 * (b - a)^2 + (36 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (24 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^2 * (c - b)^3 + (24 : ℝ) * a^2 * (c - b)^2 + (32 : ℝ) * a^1 * (b - a)^4 + (64 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (40 : ℝ) * a^1 * (b - a)^3 + (40 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (60 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (12 : ℝ) * a^1 * (b - a)^2 + (8 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (36 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^1 * (b - a)^1 * (c - b)^1 + (8 : ℝ) * a^1 * (c - b)^3 + (12 : ℝ) * a^1 * (c - b)^2 + (8 : ℝ) * (b - a)^5 + (20 : ℝ) * (b - a)^4 * (c - b)^1 + (16 : ℝ) * (b - a)^4 + (16 : ℝ) * (b - a)^3 * (c - b)^2 + (32 : ℝ) * (b - a)^3 * (c - b)^1 + (10 : ℝ) * (b - a)^3 + (4 : ℝ) * (b - a)^2 * (c - b)^3 + (20 : ℝ) * (b - a)^2 * (c - b)^2 + (15 : ℝ) * (b - a)^2 * (c - b)^1 + (2 : ℝ) * (b - a)^2 + (4 : ℝ) * (b - a)^1 * (c - b)^3 + (9 : ℝ) * (b - a)^1 * (c - b)^2 + (2 : ℝ) * (b - a)^1 * (c - b)^1 + (2 : ℝ) * (c - b)^3 + (2 : ℝ) * (c - b)^2 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^3*b^2 + 4*a^3*b + 4*a^3*c^2 + 4*a^3*c + 2*a^3 + 4*a^2*b^3 - 8*a^2*b^2*c + 8*a^2*b^2 - 8*a^2*b*c^2 - 16*a^2*b*c + 3*a^2*b + 4*a^2*c^3 + 8*a^2*c^2 + 3*a^2*c + 2*a^2 + 4*a*b^3 - 8*a*b^2*c^2 - 16*a*b^2*c + 3*a*b^2 - 16*a*b*c^2 - 24*a*b*c - 2*a*b + 4*a*c^3 + 3*a*c^2 - 2*a*c + 4*b^3*c^2 + 4*b^3*c + 2*b^3 + 4*b^2*c^3 + 8*b^2*c^2 + 3*b^2*c + 2*b^2 + 4*b*c^3 + 3*b*c^2 - 2*b*c + 2*c^3 + 2*c^2) := by
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
  have hn : 0 ≤ (4*a^3*b^2 + 4*a^3*b + 4*a^3*c^2 + 4*a^3*c + 2*a^3 + 4*a^2*b^3 - 8*a^2*b^2*c + 8*a^2*b^2 - 8*a^2*b*c^2 - 16*a^2*b*c + 3*a^2*b + 4*a^2*c^3 + 8*a^2*c^2 + 3*a^2*c + 2*a^2 + 4*a*b^3 - 8*a*b^2*c^2 - 16*a*b^2*c + 3*a*b^2 - 16*a*b*c^2 - 24*a*b*c - 2*a*b + 4*a*c^3 + 3*a*c^2 - 2*a*c + 4*b^3*c^2 + 4*b^3*c + 2*b^3 + 4*b^2*c^3 + 8*b^2*c^2 + 3*b^2*c + 2*b^2 + 4*b*c^3 + 3*b*c^2 - 2*b*c + 2*c^3 + 2*c^2) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1)) ≥ (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1))) := @solution
#print axioms solution
