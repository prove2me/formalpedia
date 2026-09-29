-- Prove2me | solution 1 for WorkbookSource.base_32836
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:47:22.041824+00:00
-- url     : https://prove2.me/submissions/95c6959e-4788-4bec-b04d-63e3d2fd871c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^2 + c^2 - a^2) / (a * (b + c)) + (c^2 + a^2 - b^2) / (b * (c + a)) + (a^2 + b^2 - c^2) / (c * (a + b)) ≥ 3 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b^2 + 2*a^4*b*c + 2*a^4*c^2 - a^3*b^2*c - a^3*b*c^2 + 2*a^2*b^4 - a^2*b^3*c - 12*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4 + 2*b^4*c^2 + 2*b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (20 : ℝ) * a^4 * (b - a)^2 + (20 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (20 : ℝ) * a^4 * (c - b)^2 + (58 : ℝ) * a^3 * (b - a)^3 + (87 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (73 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (22 : ℝ) * a^3 * (c - b)^3 + (60 : ℝ) * a^2 * (b - a)^4 + (120 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (105 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (45 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (6 : ℝ) * a^2 * (c - b)^4 + (26 : ℝ) * a^1 * (b - a)^5 + (65 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (64 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (31 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (6 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * (b - a)^6 + (12 : ℝ) * (b - a)^5 * (c - b)^1 + (14 : ℝ) * (b - a)^4 * (c - b)^2 + (8 : ℝ) * (b - a)^3 * (c - b)^3 + (2 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b^2 + 2*a^4*b*c + 2*a^4*c^2 - a^3*b^2*c - a^3*b*c^2 + 2*a^2*b^4 - a^2*b^3*c - 12*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4 + 2*b^4*c^2 + 2*b^2*c^4) := by
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
  have hn : 0 ≤ (2*a^4*b^2 + 2*a^4*b*c + 2*a^4*c^2 - a^3*b^2*c - a^3*b*c^2 + 2*a^2*b^4 - a^2*b^3*c - 12*a^2*b^2*c^2 - a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^4*c - a*b^3*c^2 - a*b^2*c^3 + 2*a*b*c^4 + 2*b^4*c^2 + 2*b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b^2 + c^2 - a^2) / (a * (b + c)) + (c^2 + a^2 - b^2) / (b * (c + a)) + (a^2 + b^2 - c^2) / (c * (a + b)) ≥ 3 / 2) := @solution
#print axioms solution
