-- Prove2me | solution 1 for WorkbookSource.base_22608
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T03:53:16.392395+00:00
-- url     : https://prove2.me/submissions/6f0f7613-bb48-4ae5-b850-3987c8400776

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 9) / (2 * a^2 + (b + c)^2) + (b^2 + 9) / (2 * b^2 + (c + a)^2) + (c^2 + 9) / (2 * c^2 + (a + b)^2) ≤ 5  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (4*a^6 + 2*a^5*b + 2*a^5*c + 2*a^4*b^2 + 4*a^4*b*c + 2*a^4*c^2 + 8*a^3*b^3 - 16*a^3*b^2*c - 16*a^3*b*c^2 + 8*a^3*c^3 + 2*a^2*b^4 - 16*a^2*b^3*c + 24*a^2*b^2*c^2 - 16*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 4*a*b^4*c - 16*a*b^3*c^2 - 16*a*b^2*c^3 + 4*a*b*c^4 + 2*a*c^5 + 4*b^6 + 2*b^5*c + 2*b^4*c^2 + 8*b^3*c^3 + 2*b^2*c^4 + 2*b*c^5 + 4*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (96 : ℝ) * a^4 * (b - a)^2 + (96 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (96 : ℝ) * a^4 * (c - b)^2 + (248 : ℝ) * a^3 * (b - a)^3 + (372 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (396 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (136 : ℝ) * a^3 * (c - b)^3 + (256 : ℝ) * a^2 * (b - a)^4 + (512 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (636 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (380 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (88 : ℝ) * a^2 * (c - b)^4 + (124 : ℝ) * a^1 * (b - a)^5 + (310 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (452 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (368 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (158 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (28 : ℝ) * a^1 * (c - b)^5 + (24 : ℝ) * (b - a)^6 + (72 : ℝ) * (b - a)^5 * (c - b)^1 + (118 : ℝ) * (b - a)^4 * (c - b)^2 + (116 : ℝ) * (b - a)^3 * (c - b)^3 + (72 : ℝ) * (b - a)^2 * (c - b)^4 + (26 : ℝ) * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (4*a^6 + 2*a^5*b + 2*a^5*c + 2*a^4*b^2 + 4*a^4*b*c + 2*a^4*c^2 + 8*a^3*b^3 - 16*a^3*b^2*c - 16*a^3*b*c^2 + 8*a^3*c^3 + 2*a^2*b^4 - 16*a^2*b^3*c + 24*a^2*b^2*c^2 - 16*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 4*a*b^4*c - 16*a*b^3*c^2 - 16*a*b^2*c^3 + 4*a*b*c^4 + 2*a*c^5 + 4*b^6 + 2*b^5*c + 2*b^4*c^2 + 8*b^3*c^3 + 2*b^2*c^4 + 2*b*c^5 + 4*c^6) := by
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
  have he : (9*a^6 + 18*a^5*b + 18*a^5*c + 30*a^4*b^2 + 46*a^4*b*c + 30*a^4*c^2 - 45*a^4 + 42*a^3*b^3 + 48*a^3*b^2*c + 48*a^3*b*c^2 - 54*a^3*b + 42*a^3*c^3 - 54*a^3*c + 30*a^2*b^4 + 48*a^2*b^3*c + 105*a^2*b^2*c^2 - 99*a^2*b^2 + 48*a^2*b*c^3 - 72*a^2*b*c + 30*a^2*c^4 - 99*a^2*c^2 + 18*a*b^5 + 46*a*b^4*c + 48*a*b^3*c^2 - 54*a*b^3 + 48*a*b^2*c^3 - 72*a*b^2*c + 46*a*b*c^4 - 72*a*b*c^2 + 18*a*c^5 - 54*a*c^3 + 9*b^6 + 18*b^5*c + 30*b^4*c^2 - 45*b^4 + 42*b^3*c^3 - 54*b^3*c + 30*b^2*c^4 - 99*b^2*c^2 + 18*b*c^5 - 54*b*c^3 + 9*c^6 - 45*c^4) = (4*a^6 + 2*a^5*b + 2*a^5*c + 2*a^4*b^2 + 4*a^4*b*c + 2*a^4*c^2 + 8*a^3*b^3 - 16*a^3*b^2*c - 16*a^3*b*c^2 + 8*a^3*c^3 + 2*a^2*b^4 - 16*a^2*b^3*c + 24*a^2*b^2*c^2 - 16*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + 4*a*b^4*c - 16*a*b^3*c^2 - 16*a*b^2*c^3 + 4*a*b*c^4 + 2*a*c^5 + 4*b^6 + 2*b^5*c + 2*b^4*c^2 + 8*b^3*c^3 + 2*b^2*c^4 + 2*b*c^5 + 4*c^6) := by
    linear_combination (5*a^5 + 11*a^4*b + 11*a^4*c + 15*a^4 + 17*a^3*b^2 + 20*a^3*b*c + 18*a^3*b + 17*a^3*c^2 + 18*a^3*c + 17*a^2*b^3 + 27*a^2*b^2*c + 33*a^2*b^2 + 27*a^2*b*c^2 + 24*a^2*b*c + 17*a^2*c^3 + 33*a^2*c^2 + 11*a*b^4 + 20*a*b^3*c + 18*a*b^3 + 27*a*b^2*c^2 + 24*a*b^2*c + 20*a*b*c^3 + 24*a*b*c^2 + 11*a*c^4 + 18*a*c^3 + 5*b^5 + 11*b^4*c + 15*b^4 + 17*b^3*c^2 + 18*b^3*c + 17*b^2*c^3 + 33*b^2*c^2 + 11*b*c^4 + 18*b*c^3 + 5*c^5 + 15*c^4) * habc
  have hn : 0 ≤ (9*a^6 + 18*a^5*b + 18*a^5*c + 30*a^4*b^2 + 46*a^4*b*c + 30*a^4*c^2 - 45*a^4 + 42*a^3*b^3 + 48*a^3*b^2*c + 48*a^3*b*c^2 - 54*a^3*b + 42*a^3*c^3 - 54*a^3*c + 30*a^2*b^4 + 48*a^2*b^3*c + 105*a^2*b^2*c^2 - 99*a^2*b^2 + 48*a^2*b*c^3 - 72*a^2*b*c + 30*a^2*c^4 - 99*a^2*c^2 + 18*a*b^5 + 46*a*b^4*c + 48*a*b^3*c^2 - 54*a*b^3 + 48*a*b^2*c^3 - 72*a*b^2*c + 46*a*b*c^4 - 72*a*b*c^2 + 18*a*c^5 - 54*a*c^3 + 9*b^6 + 18*b^5*c + 30*b^4*c^2 - 45*b^4 + 42*b^3*c^3 - 54*b^3*c + 30*b^2*c^4 - 99*b^2*c^2 + 18*b*c^5 - 54*b*c^3 + 9*c^6 - 45*c^4) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), (a^2 + 9) / (2 * a^2 + (b + c)^2) + (b^2 + 9) / (2 * b^2 + (c + a)^2) + (c^2 + 9) / (2 * c^2 + (a + b)^2) ≤ 5) := @solution
#print axioms solution
