-- Prove2me | solution 1 for WorkbookSource.base_48565
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:27:04.150332+00:00
-- url     : https://prove2.me/submissions/18557ff0-c40c-44a4-bcab-a7cc3b859ecd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (3 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (3 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) ≤ 25 / 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (24*a^6 + 12*a^5*b + 12*a^5*c - 9*a^4*b^2 + 38*a^4*b*c - 9*a^4*c^2 + 6*a^3*b^3 - 54*a^3*b^2*c - 54*a^3*b*c^2 + 6*a^3*c^3 - 9*a^2*b^4 - 54*a^2*b^3*c + 102*a^2*b^2*c^2 - 54*a^2*b*c^3 - 9*a^2*c^4 + 12*a*b^5 + 38*a*b^4*c - 54*a*b^3*c^2 - 54*a*b^2*c^3 + 38*a*b*c^4 + 12*a*c^5 + 24*b^6 + 12*b^5*c - 9*b^4*c^2 + 6*b^3*c^3 - 9*b^2*c^4 + 12*b*c^5 + 24*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (408 : ℝ) * a^4 * (b - a)^2 + (408 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (408 : ℝ) * a^4 * (c - b)^2 + (928 : ℝ) * a^3 * (b - a)^3 + (1392 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (1872 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (704 : ℝ) * a^3 * (c - b)^3 + (836 : ℝ) * a^2 * (b - a)^4 + (1672 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (2892 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (2056 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (500 : ℝ) * a^2 * (c - b)^4 + (352 : ℝ) * a^1 * (b - a)^5 + (880 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1872 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (1928 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (920 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (168 : ℝ) * a^1 * (c - b)^5 + (60 : ℝ) * (b - a)^6 + (180 : ℝ) * (b - a)^5 * (c - b)^1 + (435 : ℝ) * (b - a)^4 * (c - b)^2 + (570 : ℝ) * (b - a)^3 * (c - b)^3 + (411 : ℝ) * (b - a)^2 * (c - b)^4 + (156 : ℝ) * (b - a)^1 * (c - b)^5 + (24 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (24*a^6 + 12*a^5*b + 12*a^5*c - 9*a^4*b^2 + 38*a^4*b*c - 9*a^4*c^2 + 6*a^3*b^3 - 54*a^3*b^2*c - 54*a^3*b*c^2 + 6*a^3*c^3 - 9*a^2*b^4 - 54*a^2*b^3*c + 102*a^2*b^2*c^2 - 54*a^2*b*c^3 - 9*a^2*c^4 + 12*a*b^5 + 38*a*b^4*c - 54*a*b^3*c^2 - 54*a*b^2*c^3 + 38*a*b*c^4 + 12*a*c^5 + 24*b^6 + 12*b^5*c - 9*b^4*c^2 + 6*b^3*c^3 - 9*b^2*c^4 + 12*b*c^5 + 24*c^6) := by
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
  have hn : 0 ≤ (24*a^6 + 12*a^5*b + 12*a^5*c - 9*a^4*b^2 + 38*a^4*b*c - 9*a^4*c^2 + 6*a^3*b^3 - 54*a^3*b^2*c - 54*a^3*b*c^2 + 6*a^3*c^3 - 9*a^2*b^4 - 54*a^2*b^3*c + 102*a^2*b^2*c^2 - 54*a^2*b*c^3 - 9*a^2*c^4 + 12*a*b^5 + 38*a*b^4*c - 54*a*b^3*c^2 - 54*a*b^2*c^3 + 38*a*b*c^4 + 12*a*c^5 + 24*b^6 + 12*b^5*c - 9*b^4*c^2 + 6*b^3*c^3 - 9*b^2*c^4 + 12*b*c^5 + 24*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * a + b + c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (3 * b + c + a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (3 * c + a + b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) ≤ 25 / 2) := @solution
#print axioms solution
