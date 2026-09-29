-- Prove2me | solution 1 for WorkbookSource.plus_28597
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:33:27.79282+00:00
-- url     : https://prove2.me/submissions/45c632e4-597d-489f-8def-a5d0cb221149

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) + a * b * c ≤ 1   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6/64 + 3*a^5*b/32 + 3*a^5*c/32 + 15*a^4*b^2/64 - 21*a^4*b*c/32 + 15*a^4*c^2/64 - 11*a^3*b^3/16 + 9*a^3*b^2*c/16 + 9*a^3*b*c^2/16 - 11*a^3*c^3/16 + 15*a^2*b^4/64 + 9*a^2*b^3*c/16 - 43*a^2*b^2*c^2/32 + 9*a^2*b*c^3/16 + 15*a^2*c^4/64 + 3*a*b^5/32 - 21*a*b^4*c/32 + 9*a*b^3*c^2/16 + 9*a*b^2*c^3/16 - 21*a*b*c^4/32 + 3*a*c^5/32 + b^6/64 + 3*b^5*c/32 + 15*b^4*c^2/64 - 11*b^3*c^3/16 + 15*b^2*c^4/64 + 3*b*c^5/32 + c^6/64) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1/64 : ℝ) * a^6 + (1/16 : ℝ) * a^5 * (b - a)^1 + (1/32 : ℝ) * a^5 * (c - b)^1 + (9/16 : ℝ) * a^4 * (b - a)^2 + (9/16 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (31/64 : ℝ) * a^4 * (c - b)^2 + (3/4 : ℝ) * a^3 * (b - a)^3 + (9/8 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (11/4 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (19/16 : ℝ) * a^3 * (c - b)^3 + (1/4 : ℝ) * a^2 * (b - a)^4 + (1/2 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (4 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (15/4 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (63/64 : ℝ) * a^2 * (c - b)^4 + (9/4 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (27/8 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (27/16 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (9/32 : ℝ) * a^1 * (c - b)^5 + (3/4 : ℝ) * (b - a)^4 * (c - b)^2 + (3/2 : ℝ) * (b - a)^3 * (c - b)^3 + (15/16 : ℝ) * (b - a)^2 * (c - b)^4 + (3/16 : ℝ) * (b - a)^1 * (c - b)^5 + (1/64 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6/64 + 3*a^5*b/32 + 3*a^5*c/32 + 15*a^4*b^2/64 - 21*a^4*b*c/32 + 15*a^4*c^2/64 - 11*a^3*b^3/16 + 9*a^3*b^2*c/16 + 9*a^3*b*c^2/16 - 11*a^3*c^3/16 + 15*a^2*b^4/64 + 9*a^2*b^3*c/16 - 43*a^2*b^2*c^2/32 + 9*a^2*b*c^3/16 + 15*a^2*c^4/64 + 3*a*b^5/32 - 21*a*b^4*c/32 + 9*a*b^3*c^2/16 + 9*a*b^2*c^3/16 - 21*a*b*c^4/32 + 3*a*c^5/32 + b^6/64 + 3*b^5*c/32 + 15*b^4*c^2/64 - 11*b^3*c^3/16 + 15*b^2*c^4/64 + 3*b*c^5/32 + c^6/64) := by
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
  have he : (-a^4*b*c - a^3*b^3 - a^3*c^3 - 2*a^2*b^2*c^2 - a*b^4*c - a*b*c^4 - a*b*c - b^3*c^3 + 1) = (a^6/64 + 3*a^5*b/32 + 3*a^5*c/32 + 15*a^4*b^2/64 - 21*a^4*b*c/32 + 15*a^4*c^2/64 - 11*a^3*b^3/16 + 9*a^3*b^2*c/16 + 9*a^3*b*c^2/16 - 11*a^3*c^3/16 + 15*a^2*b^4/64 + 9*a^2*b^3*c/16 - 43*a^2*b^2*c^2/32 + 9*a^2*b*c^3/16 + 15*a^2*c^4/64 + 3*a*b^5/32 - 21*a*b^4*c/32 + 9*a*b^3*c^2/16 + 9*a*b^2*c^3/16 - 21*a*b*c^4/32 + 3*a*c^5/32 + b^6/64 + 3*b^5*c/32 + 15*b^4*c^2/64 - 11*b^3*c^3/16 + 15*b^2*c^4/64 + 3*b*c^5/32 + c^6/64) := by
    linear_combination (-a^5/64 - 5*a^4*b/64 - 5*a^4*c/64 - a^4/32 - 5*a^3*b^2/32 - 3*a^3*b*c/16 - a^3*b/8 - 5*a^3*c^2/32 - a^3*c/8 - a^3/16 - 5*a^2*b^3/32 - 7*a^2*b^2*c/32 - 3*a^2*b^2/16 - 7*a^2*b*c^2/32 - a^2*b*c/8 - 3*a^2*b/16 - 5*a^2*c^3/32 - 3*a^2*c^2/16 - 3*a^2*c/16 - a^2/8 - 5*a*b^4/64 - 3*a*b^3*c/16 - a*b^3/8 - 7*a*b^2*c^2/32 - a*b^2*c/8 - 3*a*b^2/16 - 3*a*b*c^3/16 - a*b*c^2/8 + a*b*c/8 - a*b/4 - 5*a*c^4/64 - a*c^3/8 - 3*a*c^2/16 - a*c/4 - a/4 - b^5/64 - 5*b^4*c/64 - b^4/32 - 5*b^3*c^2/32 - b^3*c/8 - b^3/16 - 5*b^2*c^3/32 - 3*b^2*c^2/16 - 3*b^2*c/16 - b^2/8 - 5*b*c^4/64 - b*c^3/8 - 3*b*c^2/16 - b*c/4 - b/4 - c^5/64 - c^4/32 - c^3/16 - c^2/8 - c/4 - 1/2) * habc
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2), (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) + a * b * c ≤ 1) := @solution
#print axioms solution
