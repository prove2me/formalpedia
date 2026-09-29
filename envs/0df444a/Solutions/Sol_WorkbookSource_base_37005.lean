-- Prove2me | solution 1 for WorkbookSource.base_37005
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T05:27:01.281837+00:00
-- url     : https://prove2.me/submissions/f756d9ee-575a-447e-be54-c63fa35a646a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (2 * a + 3 * b) + b^3 / (2 * b + 3 * c) + c^3 / (2 * c + 3 * a)) ≥ (a^2 + b^2 + c^2) / 5  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (18*a^4*b + 27*a^4*c - 18*a^3*b^2 - 15*a^3*b*c + 18*a^3*c^2 + 18*a^2*b^3 - 30*a^2*b^2*c - 30*a^2*b*c^2 - 18*a^2*c^3 + 27*a*b^4 - 15*a*b^3*c - 30*a*b^2*c^2 - 15*a*b*c^3 + 18*a*c^4 + 18*b^4*c - 18*b^3*c^2 + 18*b^2*c^3 + 27*b*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (165 : ℝ) * a^3 * (b - a)^2 + (165 : ℝ) * a^3 * (b - a)^1 * (c - b)^1 + (165 : ℝ) * a^3 * (c - b)^2 + (330 : ℝ) * a^2 * (b - a)^3 + (576 : ℝ) * a^2 * (b - a)^2 * (c - b)^1 + (576 : ℝ) * a^2 * (b - a)^1 * (c - b)^2 + (165 : ℝ) * a^2 * (c - b)^3 + (210 : ℝ) * a^1 * (b - a)^4 + (528 : ℝ) * a^1 * (b - a)^3 * (c - b)^1 + (627 : ℝ) * a^1 * (b - a)^2 * (c - b)^2 + (309 : ℝ) * a^1 * (b - a)^1 * (c - b)^3 + (45 : ℝ) * a^1 * (c - b)^4 + (45 : ℝ) * (b - a)^5 + (144 : ℝ) * (b - a)^4 * (c - b)^1 + (198 : ℝ) * (b - a)^3 * (c - b)^2 + (126 : ℝ) * (b - a)^2 * (c - b)^3 + (27 : ℝ) * (b - a)^1 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (18*a^4*b + 27*a^4*c - 18*a^3*b^2 - 15*a^3*b*c + 18*a^3*c^2 + 18*a^2*b^3 - 30*a^2*b^2*c - 30*a^2*b*c^2 - 18*a^2*c^3 + 27*a*b^4 - 15*a*b^3*c - 30*a*b^2*c^2 - 15*a*b*c^3 + 18*a*c^4 + 18*b^4*c - 18*b^3*c^2 + 18*b^2*c^3 + 27*b*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (165 : ℝ) * a^3 * (c - a)^2 + (165 : ℝ) * a^3 * (c - a)^1 * (b - c)^1 + (165 : ℝ) * a^3 * (b - c)^2 + (330 : ℝ) * a^2 * (c - a)^3 + (414 : ℝ) * a^2 * (c - a)^2 * (b - c)^1 + (414 : ℝ) * a^2 * (c - a)^1 * (b - c)^2 + (165 : ℝ) * a^2 * (b - c)^3 + (210 : ℝ) * a^1 * (c - a)^4 + (312 : ℝ) * a^1 * (c - a)^3 * (b - c)^1 + (303 : ℝ) * a^1 * (c - a)^2 * (b - c)^2 + (201 : ℝ) * a^1 * (c - a)^1 * (b - c)^3 + (45 : ℝ) * a^1 * (b - c)^4 + (45 : ℝ) * (c - a)^5 + (81 : ℝ) * (c - a)^4 * (b - c)^1 + (72 : ℝ) * (c - a)^3 * (b - c)^2 + (54 : ℝ) * (c - a)^2 * (b - c)^3 + (18 : ℝ) * (c - a)^1 * (b - c)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (18*a^4*b + 27*a^4*c - 18*a^3*b^2 - 15*a^3*b*c + 18*a^3*c^2 + 18*a^2*b^3 - 30*a^2*b^2*c - 30*a^2*b*c^2 - 18*a^2*c^3 + 27*a*b^4 - 15*a*b^3*c - 30*a*b^2*c^2 - 15*a*b*c^3 + 18*a*c^4 + 18*b^4*c - 18*b^3*c^2 + 18*b^2*c^3 + 27*b*c^4) := by
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
  have hn : 0 ≤ (18*a^4*b + 27*a^4*c - 18*a^3*b^2 - 15*a^3*b*c + 18*a^3*c^2 + 18*a^2*b^3 - 30*a^2*b^2*c - 30*a^2*b*c^2 - 18*a^2*c^3 + 27*a*b^4 - 15*a*b^3*c - 30*a*b^2*c^2 - 15*a*b*c^3 + 18*a*c^4 + 18*b^4*c - 18*b^3*c^2 + 18*b^2*c^3 + 27*b*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^3 / (2 * a + 3 * b) + b^3 / (2 * b + 3 * c) + c^3 / (2 * c + 3 * a)) ≥ (a^2 + b^2 + c^2) / 5) := @solution
#print axioms solution
