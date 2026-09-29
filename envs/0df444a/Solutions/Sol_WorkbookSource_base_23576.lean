-- Prove2me | solution 1 for WorkbookSource.base_23576
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:29.355467+00:00
-- url     : https://prove2.me/submissions/45812d33-24bc-4176-a2a0-998d214120b1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (h : a + b + c = 2) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0): (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≤ 2  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6/32 + 3*a^5*b/16 + 3*a^5*c/16 - 17*a^4*b^2/32 + 15*a^4*b*c/16 - 17*a^4*c^2/32 + 5*a^3*b^3/8 + 15*a^3*b^2*c/8 + 15*a^3*b*c^2/8 + 5*a^3*c^3/8 - 17*a^2*b^4/32 + 15*a^2*b^3*c/8 - 3*a^2*b^2*c^2/16 + 15*a^2*b*c^3/8 - 17*a^2*c^4/32 + 3*a*b^5/16 + 15*a*b^4*c/16 + 15*a*b^3*c^2/8 + 15*a*b^2*c^3/8 + 15*a*b*c^4/16 + 3*a*c^5/16 + b^6/32 + 3*b^5*c/16 - 17*b^4*c^2/32 + 5*b^3*c^3/8 - 17*b^2*c^4/32 + 3*b*c^5/16 + c^6/32) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (441/32 : ℝ) * a^6 + (441/8 : ℝ) * a^5 * (b - a)^1 + (441/16 : ℝ) * a^5 * (c - b)^1 + (719/8 : ℝ) * a^4 * (b - a)^2 + (719/8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (671/32 : ℝ) * a^4 * (c - b)^2 + (75 : ℝ) * a^3 * (b - a)^3 + (225/2 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (221/4 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (71/8 : ℝ) * a^3 * (c - b)^3 + (65/2 : ℝ) * a^2 * (b - a)^4 + (65 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (201/4 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (71/4 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (71/32 : ℝ) * a^2 * (c - b)^4 + (6 : ℝ) * a^1 * (b - a)^5 + (15 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (17 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (21/2 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (29/8 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (9/16 : ℝ) * a^1 * (c - b)^5 + (1/2 : ℝ) * (b - a)^4 * (c - b)^2 + (1 : ℝ) * (b - a)^3 * (c - b)^3 + (7/8 : ℝ) * (b - a)^2 * (c - b)^4 + (3/8 : ℝ) * (b - a)^1 * (c - b)^5 + (1/32 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6/32 + 3*a^5*b/16 + 3*a^5*c/16 - 17*a^4*b^2/32 + 15*a^4*b*c/16 - 17*a^4*c^2/32 + 5*a^3*b^3/8 + 15*a^3*b^2*c/8 + 15*a^3*b*c^2/8 + 5*a^3*c^3/8 - 17*a^2*b^4/32 + 15*a^2*b^3*c/8 - 3*a^2*b^2*c^2/16 + 15*a^2*b*c^3/8 - 17*a^2*c^4/32 + 3*a*b^5/16 + 15*a*b^4*c/16 + 15*a*b^3*c^2/8 + 15*a*b^2*c^3/8 + 15*a*b*c^4/16 + 3*a*c^5/16 + b^6/32 + 3*b^5*c/16 - 17*b^4*c^2/32 + 5*b^3*c^3/8 - 17*b^2*c^4/32 + 3*b*c^5/16 + c^6/32) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        convert haux a b c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          convert haux a c b (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c a b (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        convert haux b a c (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          convert haux b c a (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux c b a (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-a^4*b^2 - a^4*c^2 - a^2*b^4 - 3*a^2*b^2*c^2 - a^2*c^4 - b^4*c^2 - b^2*c^4 + 2) = (a^6/32 + 3*a^5*b/16 + 3*a^5*c/16 - 17*a^4*b^2/32 + 15*a^4*b*c/16 - 17*a^4*c^2/32 + 5*a^3*b^3/8 + 15*a^3*b^2*c/8 + 15*a^3*b*c^2/8 + 5*a^3*c^3/8 - 17*a^2*b^4/32 + 15*a^2*b^3*c/8 - 3*a^2*b^2*c^2/16 + 15*a^2*b*c^3/8 - 17*a^2*c^4/32 + 3*a*b^5/16 + 15*a*b^4*c/16 + 15*a*b^3*c^2/8 + 15*a*b^2*c^3/8 + 15*a*b*c^4/16 + 3*a*c^5/16 + b^6/32 + 3*b^5*c/16 - 17*b^4*c^2/32 + 5*b^3*c^3/8 - 17*b^2*c^4/32 + 3*b*c^5/16 + c^6/32) := by
    linear_combination (-a^5/32 - 5*a^4*b/32 - 5*a^4*c/32 - a^4/16 - 5*a^3*b^2/16 - 5*a^3*b*c/8 - a^3*b/4 - 5*a^3*c^2/16 - a^3*c/4 - a^3/8 - 5*a^2*b^3/16 - 15*a^2*b^2*c/16 - 3*a^2*b^2/8 - 15*a^2*b*c^2/16 - 3*a^2*b*c/4 - 3*a^2*b/8 - 5*a^2*c^3/16 - 3*a^2*c^2/8 - 3*a^2*c/8 - a^2/4 - 5*a*b^4/32 - 5*a*b^3*c/8 - a*b^3/4 - 15*a*b^2*c^2/16 - 3*a*b^2*c/4 - 3*a*b^2/8 - 5*a*b*c^3/8 - 3*a*b*c^2/4 - 3*a*b*c/4 - a*b/2 - 5*a*c^4/32 - a*c^3/4 - 3*a*c^2/8 - a*c/2 - a/2 - b^5/32 - 5*b^4*c/32 - b^4/16 - 5*b^3*c^2/16 - b^3*c/4 - b^3/8 - 5*b^2*c^3/16 - 3*b^2*c^2/8 - 3*b^2*c/8 - b^2/4 - 5*b*c^4/32 - b*c^3/4 - 3*b*c^2/8 - b*c/2 - b/2 - c^5/32 - c^4/16 - c^3/8 - c^2/4 - c/2 - 1) * h
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (h : a + b + c = 2) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≤ 2) := @solution
#print axioms solution
