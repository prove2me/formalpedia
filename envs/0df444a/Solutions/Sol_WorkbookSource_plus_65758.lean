-- Prove2me | solution 1 for WorkbookSource.plus_65758
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:26.577645+00:00
-- url     : https://prove2.me/submissions/4fc8e69c-35f3-45e1-940b-70db6ccacca3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (2 * a + b + c) + (b + c) / (2 * b + c + a) + (c + a) / (2 * c + a + b) ≤ 1 / 2 * (a / b + b / c + c / a)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^5*c + 2*a^4*b^2 + a^4*b*c + 7*a^4*c^2 + 7*a^3*b^3 - 8*a^3*b^2*c - 2*a^3*b*c^2 + 7*a^3*c^3 + 7*a^2*b^4 - 2*a^2*b^3*c - 27*a^2*b^2*c^2 - 8*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + a*b^4*c - 8*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 2*b^4*c^2 + 7*b^3*c^3 + 7*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^4 * (b - a)^2 + (64 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (64 : ℝ) * a^4 * (c - b)^2 + (192 : ℝ) * a^3 * (b - a)^3 + (321 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (257 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (64 : ℝ) * a^3 * (c - b)^3 + (212 : ℝ) * a^2 * (b - a)^4 + (490 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (447 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (169 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (20 : ℝ) * a^2 * (c - b)^4 + (102 : ℝ) * a^1 * (b - a)^5 + (298 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (332 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (167 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (35 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (2 : ℝ) * a^1 * (c - b)^5 + (18 : ℝ) * (b - a)^6 + (63 : ℝ) * (b - a)^5 * (c - b)^1 + (85 : ℝ) * (b - a)^4 * (c - b)^2 + (55 : ℝ) * (b - a)^3 * (c - b)^3 + (17 : ℝ) * (b - a)^2 * (c - b)^4 + (2 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (2*a^5*c + 2*a^4*b^2 + a^4*b*c + 7*a^4*c^2 + 7*a^3*b^3 - 8*a^3*b^2*c - 2*a^3*b*c^2 + 7*a^3*c^3 + 7*a^2*b^4 - 2*a^2*b^3*c - 27*a^2*b^2*c^2 - 8*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + a*b^4*c - 8*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 2*b^4*c^2 + 7*b^3*c^3 + 7*b^2*c^4 + 2*b*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (64 : ℝ) * a^4 * (c - a)^2 + (64 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (64 : ℝ) * a^4 * (b - c)^2 + (192 : ℝ) * a^3 * (c - a)^3 + (255 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (191 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (64 : ℝ) * a^3 * (b - c)^3 + (212 : ℝ) * a^2 * (c - a)^4 + (358 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (249 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (103 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (20 : ℝ) * a^2 * (b - c)^4 + (102 : ℝ) * a^1 * (c - a)^5 + (212 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (160 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (61 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (15 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (2 : ℝ) * a^1 * (b - c)^5 + (18 : ℝ) * (c - a)^6 + (45 : ℝ) * (c - a)^5 * (b - c)^1 + (40 : ℝ) * (c - a)^4 * (b - c)^2 + (15 : ℝ) * (c - a)^3 * (b - c)^3 + (2 : ℝ) * (c - a)^2 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^5*c + 2*a^4*b^2 + a^4*b*c + 7*a^4*c^2 + 7*a^3*b^3 - 8*a^3*b^2*c - 2*a^3*b*c^2 + 7*a^3*c^3 + 7*a^2*b^4 - 2*a^2*b^3*c - 27*a^2*b^2*c^2 - 8*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + a*b^4*c - 8*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 2*b^4*c^2 + 7*b^3*c^3 + 7*b^2*c^4 + 2*b*c^5) := by
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
  have hn : 0 ≤ (2*a^5*c + 2*a^4*b^2 + a^4*b*c + 7*a^4*c^2 + 7*a^3*b^3 - 8*a^3*b^2*c - 2*a^3*b*c^2 + 7*a^3*c^3 + 7*a^2*b^4 - 2*a^2*b^3*c - 27*a^2*b^2*c^2 - 8*a^2*b*c^3 + 2*a^2*c^4 + 2*a*b^5 + a*b^4*c - 8*a*b^3*c^2 - 2*a*b^2*c^3 + a*b*c^4 + 2*b^4*c^2 + 7*b^3*c^3 + 7*b^2*c^4 + 2*b*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b) / (2 * a + b + c) + (b + c) / (2 * b + c + a) + (c + a) / (2 * c + a + b) ≤ 1 / 2 * (a / b + b / c + c / a)) := @solution
#print axioms solution
