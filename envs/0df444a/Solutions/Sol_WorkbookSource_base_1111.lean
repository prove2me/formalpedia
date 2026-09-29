-- Prove2me | solution 1 for WorkbookSource.base_1111
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:26.176934+00:00
-- url     : https://prove2.me/submissions/a9471d87-cb92-48cc-b1e5-664fe2fbcf3c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 * a ^ 2 + 9 * b * c) / (b + c) ^ 2 + (4 * b ^ 2 + 9 * c * a) / (c + a) ^ 2 + (4 * c ^ 2 + 9 * a * b) / (a + b) ^ 2 ≥ 39 / 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (16*a^6 + 32*a^5*b + 32*a^5*c - 23*a^4*b^2 + 22*a^4*b*c - 23*a^4*c^2 - 42*a^3*b^3 - 22*a^3*b^2*c - 22*a^3*b*c^2 - 42*a^3*c^3 - 23*a^2*b^4 - 22*a^2*b^3*c + 90*a^2*b^2*c^2 - 22*a^2*b*c^3 - 23*a^2*c^4 + 32*a*b^5 + 22*a*b^4*c - 22*a*b^3*c^2 - 22*a*b^2*c^3 + 22*a*b*c^4 + 32*a*c^5 + 16*b^6 + 32*b^5*c - 23*b^4*c^2 - 42*b^3*c^3 - 23*b^2*c^4 + 32*b*c^5 + 16*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (352 : ℝ) * a^4 * (b - a)^2 + (352 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (352 : ℝ) * a^4 * (c - b)^2 + (672 : ℝ) * a^3 * (b - a)^3 + (1008 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1808 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (736 : ℝ) * a^3 * (c - b)^3 + (440 : ℝ) * a^2 * (b - a)^4 + (880 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2616 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (2176 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (536 : ℝ) * a^2 * (c - b)^4 + (112 : ℝ) * a^1 * (b - a)^5 + (280 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1456 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1904 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (936 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (160 : ℝ) * a^1 * (c - b)^5 + (8 : ℝ) * (b - a)^6 + (24 : ℝ) * (b - a)^5 * (c - b)^1 + (273 : ℝ) * (b - a)^4 * (c - b)^2 + (506 : ℝ) * (b - a)^3 * (c - b)^3 + (377 : ℝ) * (b - a)^2 * (c - b)^4 + (128 : ℝ) * (b - a)^1 * (c - b)^5 + (16 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (16*a^6 + 32*a^5*b + 32*a^5*c - 23*a^4*b^2 + 22*a^4*b*c - 23*a^4*c^2 - 42*a^3*b^3 - 22*a^3*b^2*c - 22*a^3*b*c^2 - 42*a^3*c^3 - 23*a^2*b^4 - 22*a^2*b^3*c + 90*a^2*b^2*c^2 - 22*a^2*b*c^3 - 23*a^2*c^4 + 32*a*b^5 + 22*a*b^4*c - 22*a*b^3*c^2 - 22*a*b^2*c^3 + 22*a*b*c^4 + 32*a*c^5 + 16*b^6 + 32*b^5*c - 23*b^4*c^2 - 42*b^3*c^3 - 23*b^2*c^4 + 32*b*c^5 + 16*c^6) := by
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
  have hn : 0 ≤ (16*a^6 + 32*a^5*b + 32*a^5*c - 23*a^4*b^2 + 22*a^4*b*c - 23*a^4*c^2 - 42*a^3*b^3 - 22*a^3*b^2*c - 22*a^3*b*c^2 - 42*a^3*c^3 - 23*a^2*b^4 - 22*a^2*b^3*c + 90*a^2*b^2*c^2 - 22*a^2*b*c^3 - 23*a^2*c^4 + 32*a*b^5 + 22*a*b^4*c - 22*a*b^3*c^2 - 22*a*b^2*c^3 + 22*a*b*c^4 + 32*a*c^5 + 16*b^6 + 32*b^5*c - 23*b^4*c^2 - 42*b^3*c^3 - 23*b^2*c^4 + 32*b*c^5 + 16*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (4 * a ^ 2 + 9 * b * c) / (b + c) ^ 2 + (4 * b ^ 2 + 9 * c * a) / (c + a) ^ 2 + (4 * c ^ 2 + 9 * a * b) / (a + b) ^ 2 ≥ 39 / 4) := @solution
#print axioms solution
