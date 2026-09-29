-- Prove2me | solution 1 for WorkbookSource.base_26251
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:07:51.735156+00:00
-- url     : https://prove2.me/submissions/d60db6bc-7935-49cc-8ec6-a823cff90d94

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) / (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)) ≥ 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (3*a^5*b - 4*a^4*b^2 - 3*a^4*b*c + a^4*c^2 + 3*a^3*b^3 - 4*a^3*b^2*c + 4*a^3*b*c^2 + 3*a^3*c^3 + a^2*b^4 + 4*a^2*b^3*c - 4*a^2*b*c^3 - 4*a^2*c^4 - 3*a*b^4*c - 4*a*b^3*c^2 + 4*a*b^2*c^3 - 3*a*b*c^4 + 3*a*c^5 + 3*b^5*c - 4*b^4*c^2 + 3*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^4 * (b - a)^2 + (9 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (9 : ℝ) * a^4 * (c - b)^2 + (24 : ℝ) * a^3 * (b - a)^3 + (45 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (45 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (12 : ℝ) * a^3 * (c - b)^3 + (27 : ℝ) * a^2 * (b - a)^4 + (72 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (90 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (45 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (9 : ℝ) * a^2 * (c - b)^4 + (15 : ℝ) * a^1 * (b - a)^5 + (44 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (64 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (43 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (14 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (3 : ℝ) * a^1 * (c - b)^5 + (3 : ℝ) * (b - a)^6 + (8 : ℝ) * (b - a)^5 * (c - b)^1 + (11 : ℝ) * (b - a)^4 * (c - b)^2 + (7 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (3*a^5*b - 4*a^4*b^2 - 3*a^4*b*c + a^4*c^2 + 3*a^3*b^3 - 4*a^3*b^2*c + 4*a^3*b*c^2 + 3*a^3*c^3 + a^2*b^4 + 4*a^2*b^3*c - 4*a^2*b*c^3 - 4*a^2*c^4 - 3*a*b^4*c - 4*a*b^3*c^2 + 4*a*b^2*c^3 - 3*a*b*c^4 + 3*a*c^5 + 3*b^5*c - 4*b^4*c^2 + 3*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (9 : ℝ) * a^4 * (c - a)^2 + (9 : ℝ) * a^4 * (c - a)^1 * (b - c)^1 + (9 : ℝ) * a^4 * (b - c)^2 + (24 : ℝ) * a^3 * (c - a)^3 + (27 : ℝ) * a^3 * (c - a)^2 * (b - c)^1 + (27 : ℝ) * a^3 * (c - a)^1 * (b - c)^2 + (12 : ℝ) * a^3 * (b - c)^3 + (27 : ℝ) * a^2 * (c - a)^4 + (36 : ℝ) * a^2 * (c - a)^3 * (b - c)^1 + (36 : ℝ) * a^2 * (c - a)^2 * (b - c)^2 + (27 : ℝ) * a^2 * (c - a)^1 * (b - c)^3 + (9 : ℝ) * a^2 * (b - c)^4 + (15 : ℝ) * a^1 * (c - a)^5 + (31 : ℝ) * a^1 * (c - a)^4 * (b - c)^1 + (38 : ℝ) * a^1 * (c - a)^3 * (b - c)^2 + (35 : ℝ) * a^1 * (c - a)^2 * (b - c)^3 + (19 : ℝ) * a^1 * (c - a)^1 * (b - c)^4 + (3 : ℝ) * a^1 * (b - c)^5 + (3 : ℝ) * (c - a)^6 + (10 : ℝ) * (c - a)^5 * (b - c)^1 + (16 : ℝ) * (c - a)^4 * (b - c)^2 + (17 : ℝ) * (c - a)^3 * (b - c)^3 + (11 : ℝ) * (c - a)^2 * (b - c)^4 + (3 : ℝ) * (c - a)^1 * (b - c)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (3*a^5*b - 4*a^4*b^2 - 3*a^4*b*c + a^4*c^2 + 3*a^3*b^3 - 4*a^3*b^2*c + 4*a^3*b*c^2 + 3*a^3*c^3 + a^2*b^4 + 4*a^2*b^3*c - 4*a^2*b*c^3 - 4*a^2*c^4 - 3*a*b^4*c - 4*a*b^3*c^2 + 4*a*b^2*c^3 - 3*a*b*c^4 + 3*a*c^5 + 3*b^5*c - 4*b^4*c^2 + 3*b^3*c^3 + b^2*c^4) := by
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
  have hn : 0 ≤ (3*a^5*b - 4*a^4*b^2 - 3*a^4*b*c + a^4*c^2 + 3*a^3*b^3 - 4*a^3*b^2*c + 4*a^3*b*c^2 + 3*a^3*c^3 + a^2*b^4 + 4*a^2*b^3*c - 4*a^2*b*c^3 - 4*a^2*c^4 - 3*a*b^4*c - 4*a*b^3*c^2 + 4*a*b^2*c^3 - 3*a*b*c^4 + 3*a*c^5 + 3*b^5*c - 4*b^4*c^2 + 3*b^3*c^3 + b^2*c^4) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) / (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)) ≥ 4) := @solution
#print axioms solution
