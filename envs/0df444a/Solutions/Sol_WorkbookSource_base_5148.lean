-- Prove2me | solution 1 for WorkbookSource.base_5148
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:15:19.795815+00:00
-- url     : https://prove2.me/submissions/cb23fe12-65ca-4548-a98a-fcb601fc85c0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a) ≥ (1 / 2) * ((a + c) ^ 2 / (b + c) + (b + a) ^ 2 / (c + a) + (c + b) ^ 2 / (a + b))  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b*c + 2*a^5*c^2 + 2*a^4*c^3 + 2*a^3*b^4 - a^3*b^3*c - 4*a^3*b^2*c^2 - a^3*b*c^3 + 2*a^2*b^5 - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 + a*b^5*c - a*b^3*c^3 + a*b*c^5 + 2*b^3*c^4 + 2*b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^5 * (b - a)^2 + (24 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (24 : ℝ) * a^5 * (c - b)^2 + (86 : ℝ) * a^4 * (b - a)^3 + (150 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (132 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (34 : ℝ) * a^4 * (c - b)^3 + (121 : ℝ) * a^3 * (b - a)^4 + (298 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (307 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (130 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (17 : ℝ) * a^3 * (c - b)^4 + (84 : ℝ) * a^2 * (b - a)^5 + (265 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (332 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (191 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (46 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (3 : ℝ) * a^2 * (c - b)^5 + (29 : ℝ) * a^1 * (b - a)^6 + (111 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (167 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (121 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (41 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (5 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (4 : ℝ) * (b - a)^7 + (18 : ℝ) * (b - a)^6 * (c - b)^1 + (32 : ℝ) * (b - a)^5 * (c - b)^2 + (28 : ℝ) * (b - a)^4 * (c - b)^3 + (12 : ℝ) * (b - a)^3 * (c - b)^4 + (2 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have haux1 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ c) (hord2 : c ≤ b) : 0 ≤ (a^5*b*c + 2*a^5*c^2 + 2*a^4*c^3 + 2*a^3*b^4 - a^3*b^3*c - 4*a^3*b^2*c^2 - a^3*b*c^3 + 2*a^2*b^5 - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 + a*b^5*c - a*b^3*c^3 + a*b*c^5 + 2*b^3*c^4 + 2*b^2*c^5) := by
    have hdiff1 : 0 ≤ (c - a) := by linarith
    have hdiff2 : 0 ≤ (b - c) := by linarith
    have hpos : 0 ≤ (24 : ℝ) * a^5 * (c - a)^2 + (24 : ℝ) * a^5 * (c - a)^1 * (b - c)^1 + (24 : ℝ) * a^5 * (b - c)^2 + (86 : ℝ) * a^4 * (c - a)^3 + (108 : ℝ) * a^4 * (c - a)^2 * (b - c)^1 + (90 : ℝ) * a^4 * (c - a)^1 * (b - c)^2 + (34 : ℝ) * a^4 * (b - c)^3 + (121 : ℝ) * a^3 * (c - a)^4 + (186 : ℝ) * a^3 * (c - a)^3 * (b - c)^1 + (139 : ℝ) * a^3 * (c - a)^2 * (b - c)^2 + (74 : ℝ) * a^3 * (c - a)^1 * (b - c)^3 + (17 : ℝ) * a^3 * (b - c)^4 + (84 : ℝ) * a^2 * (c - a)^5 + (155 : ℝ) * a^2 * (c - a)^4 * (b - c)^1 + (112 : ℝ) * a^2 * (c - a)^3 * (b - c)^2 + (55 : ℝ) * a^2 * (c - a)^2 * (b - c)^3 + (20 : ℝ) * a^2 * (c - a)^1 * (b - c)^4 + (3 : ℝ) * a^2 * (b - c)^5 + (29 : ℝ) * a^1 * (c - a)^6 + (63 : ℝ) * a^1 * (c - a)^5 * (b - c)^1 + (47 : ℝ) * a^1 * (c - a)^4 * (b - c)^2 + (17 : ℝ) * a^1 * (c - a)^3 * (b - c)^3 + (5 : ℝ) * a^1 * (c - a)^2 * (b - c)^4 + (1 : ℝ) * a^1 * (c - a)^1 * (b - c)^5 + (4 : ℝ) * (c - a)^7 + (10 : ℝ) * (c - a)^6 * (b - c)^1 + (8 : ℝ) * (c - a)^5 * (b - c)^2 + (2 : ℝ) * (c - a)^4 * (b - c)^3 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b*c + 2*a^5*c^2 + 2*a^4*c^3 + 2*a^3*b^4 - a^3*b^3*c - 4*a^3*b^2*c^2 - a^3*b*c^3 + 2*a^2*b^5 - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 + a*b^5*c - a*b^3*c^3 + a*b*c^5 + 2*b^3*c^4 + 2*b^2*c^5) := by
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
  have hn : 0 ≤ (a^5*b*c + 2*a^5*c^2 + 2*a^4*c^3 + 2*a^3*b^4 - a^3*b^3*c - 4*a^3*b^2*c^2 - a^3*b*c^3 + 2*a^2*b^5 - 4*a^2*b^3*c^2 - 4*a^2*b^2*c^3 + a*b^5*c - a*b^3*c^3 + a*b*c^5 + 2*b^3*c^4 + 2*b^2*c^5) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 / b + b^2 / c + c^2 / a) ≥ (1 / 2) * ((a + c) ^ 2 / (b + c) + (b + a) ^ 2 / (c + a) + (c + b) ^ 2 / (a + b))) := @solution
#print axioms solution
