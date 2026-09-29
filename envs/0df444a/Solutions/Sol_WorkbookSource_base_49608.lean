-- Prove2me | solution 1 for WorkbookSource.base_49608
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:27.02686+00:00
-- url     : https://prove2.me/submissions/3eddbbb8-5e14-41e1-8b2c-6d4804b73eca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : (a + b) ^ 2 * (a + c) ^ 2 * (b + c) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 8  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^8/32 + a^7*b/4 + a^7*c/4 - a^6*b^2/8 - a^6*b*c/4 - a^6*c^2/8 - a^5*b^3/4 - 3*a^5*b^2*c/4 - 3*a^5*b*c^2/4 - a^5*c^3/4 + 3*a^4*b^4/16 + 3*a^4*b^3*c/4 + 9*a^4*b^2*c^2/8 + 3*a^4*b*c^3/4 + 3*a^4*c^4/16 - a^3*b^5/4 + 3*a^3*b^4*c/4 + 7*a^3*b^3*c^2/2 + 7*a^3*b^2*c^3/2 + 3*a^3*b*c^4/4 - a^3*c^5/4 - a^2*b^6/8 - 3*a^2*b^5*c/4 + 9*a^2*b^4*c^2/8 + 7*a^2*b^3*c^3/2 + 9*a^2*b^2*c^4/8 - 3*a^2*b*c^5/4 - a^2*c^6/8 + a*b^7/4 - a*b^6*c/4 - 3*a*b^5*c^2/4 + 3*a*b^4*c^3/4 + 3*a*b^3*c^4/4 - 3*a*b^2*c^5/4 - a*b*c^6/4 + a*c^7/4 + b^8/32 + b^7*c/4 - b^6*c^2/8 - b^5*c^3/4 + 3*b^4*c^4/16 - b^3*c^5/4 - b^2*c^6/8 + b*c^7/4 + c^8/32) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (417/32 : ℝ) * a^8 + (139/2 : ℝ) * a^7 * (b - a)^1 + (139/4 : ℝ) * a^7 * (c - b)^1 + (303/2 : ℝ) * a^6 * (b - a)^2 + (303/2 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (239/8 : ℝ) * a^6 * (c - b)^2 + (170 : ℝ) * a^5 * (b - a)^3 + (255 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (207/2 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (37/4 : ℝ) * a^5 * (c - b)^3 + (103 : ℝ) * a^4 * (b - a)^4 + (206 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (273/2 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (67/2 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (83/16 : ℝ) * a^4 * (c - b)^4 + (32 : ℝ) * a^3 * (b - a)^5 + (80 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (92 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (58 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (57/2 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (29/4 : ℝ) * a^3 * (c - b)^5 + (4 : ℝ) * a^2 * (b - a)^6 + (12 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (39 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (58 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (99/2 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (45/2 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (31/8 : ℝ) * a^2 * (c - b)^6 + (12 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (30 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (34 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (21 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (13/2 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (3/4 : ℝ) * a^1 * (c - b)^7 + (2 : ℝ) * (b - a)^6 * (c - b)^2 + (6 : ℝ) * (b - a)^5 * (c - b)^3 + (8 : ℝ) * (b - a)^4 * (c - b)^4 + (6 : ℝ) * (b - a)^3 * (c - b)^5 + (5/2 : ℝ) * (b - a)^2 * (c - b)^6 + (1/2 : ℝ) * (b - a)^1 * (c - b)^7 + (1/32 : ℝ) * (c - b)^8 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^8/32 + a^7*b/4 + a^7*c/4 - a^6*b^2/8 - a^6*b*c/4 - a^6*c^2/8 - a^5*b^3/4 - 3*a^5*b^2*c/4 - 3*a^5*b*c^2/4 - a^5*c^3/4 + 3*a^4*b^4/16 + 3*a^4*b^3*c/4 + 9*a^4*b^2*c^2/8 + 3*a^4*b*c^3/4 + 3*a^4*c^4/16 - a^3*b^5/4 + 3*a^3*b^4*c/4 + 7*a^3*b^3*c^2/2 + 7*a^3*b^2*c^3/2 + 3*a^3*b*c^4/4 - a^3*c^5/4 - a^2*b^6/8 - 3*a^2*b^5*c/4 + 9*a^2*b^4*c^2/8 + 7*a^2*b^3*c^3/2 + 9*a^2*b^2*c^4/8 - 3*a^2*b*c^5/4 - a^2*c^6/8 + a*b^7/4 - a*b^6*c/4 - 3*a*b^5*c^2/4 + 3*a*b^4*c^3/4 + 3*a*b^3*c^4/4 - 3*a*b^2*c^5/4 - a*b*c^6/4 + a*c^7/4 + b^8/32 + b^7*c/4 - b^6*c^2/8 - b^5*c^3/4 + 3*b^4*c^4/16 - b^3*c^5/4 - b^2*c^6/8 + b*c^7/4 + c^8/32) := by
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
  have he : (-a^6*b^2 - 2*a^6*b*c - a^6*c^2 - 2*a^5*b^3 - 6*a^5*b^2*c - 6*a^5*b*c^2 - 2*a^5*c^3 - 2*a^4*b^4 - 8*a^4*b^3*c - 12*a^4*b^2*c^2 - 8*a^4*b*c^3 - 2*a^4*c^4 - 2*a^3*b^5 - 8*a^3*b^4*c - 14*a^3*b^3*c^2 - 14*a^3*b^2*c^3 - 8*a^3*b*c^4 - 2*a^3*c^5 - a^2*b^6 - 6*a^2*b^5*c - 12*a^2*b^4*c^2 - 14*a^2*b^3*c^3 - 12*a^2*b^2*c^4 - 6*a^2*b*c^5 - a^2*c^6 - 2*a*b^6*c - 6*a*b^5*c^2 - 8*a*b^4*c^3 - 8*a*b^3*c^4 - 6*a*b^2*c^5 - 2*a*b*c^6 - b^6*c^2 - 2*b^5*c^3 - 2*b^4*c^4 - 2*b^3*c^5 - b^2*c^6 + 8) = (a^8/32 + a^7*b/4 + a^7*c/4 - a^6*b^2/8 - a^6*b*c/4 - a^6*c^2/8 - a^5*b^3/4 - 3*a^5*b^2*c/4 - 3*a^5*b*c^2/4 - a^5*c^3/4 + 3*a^4*b^4/16 + 3*a^4*b^3*c/4 + 9*a^4*b^2*c^2/8 + 3*a^4*b*c^3/4 + 3*a^4*c^4/16 - a^3*b^5/4 + 3*a^3*b^4*c/4 + 7*a^3*b^3*c^2/2 + 7*a^3*b^2*c^3/2 + 3*a^3*b*c^4/4 - a^3*c^5/4 - a^2*b^6/8 - 3*a^2*b^5*c/4 + 9*a^2*b^4*c^2/8 + 7*a^2*b^3*c^3/2 + 9*a^2*b^2*c^4/8 - 3*a^2*b*c^5/4 - a^2*c^6/8 + a*b^7/4 - a*b^6*c/4 - 3*a*b^5*c^2/4 + 3*a*b^4*c^3/4 + 3*a*b^3*c^4/4 - 3*a*b^2*c^5/4 - a*b*c^6/4 + a*c^7/4 + b^8/32 + b^7*c/4 - b^6*c^2/8 - b^5*c^3/4 + 3*b^4*c^4/16 - b^3*c^5/4 - b^2*c^6/8 + b*c^7/4 + c^8/32) := by
    linear_combination (-a^7/32 - 7*a^6*b/32 - 7*a^6*c/32 - a^6/16 - 21*a^5*b^2/32 - 21*a^5*b*c/16 - 3*a^5*b/8 - 21*a^5*c^2/32 - 3*a^5*c/8 - a^5/8 - 35*a^4*b^3/32 - 105*a^4*b^2*c/32 - 15*a^4*b^2/16 - 105*a^4*b*c^2/32 - 15*a^4*b*c/8 - 5*a^4*b/8 - 35*a^4*c^3/32 - 15*a^4*c^2/16 - 5*a^4*c/8 - a^4/4 - 35*a^3*b^4/32 - 35*a^3*b^3*c/8 - 5*a^3*b^3/4 - 105*a^3*b^2*c^2/16 - 15*a^3*b^2*c/4 - 5*a^3*b^2/4 - 35*a^3*b*c^3/8 - 15*a^3*b*c^2/4 - 5*a^3*b*c/2 - a^3*b - 35*a^3*c^4/32 - 5*a^3*c^3/4 - 5*a^3*c^2/4 - a^3*c - a^3/2 - 21*a^2*b^5/32 - 105*a^2*b^4*c/32 - 15*a^2*b^4/16 - 105*a^2*b^3*c^2/16 - 15*a^2*b^3*c/4 - 5*a^2*b^3/4 - 105*a^2*b^2*c^3/16 - 45*a^2*b^2*c^2/8 - 15*a^2*b^2*c/4 - 3*a^2*b^2/2 - 105*a^2*b*c^4/32 - 15*a^2*b*c^3/4 - 15*a^2*b*c^2/4 - 3*a^2*b*c - 3*a^2*b/2 - 21*a^2*c^5/32 - 15*a^2*c^4/16 - 5*a^2*c^3/4 - 3*a^2*c^2/2 - 3*a^2*c/2 - a^2 - 7*a*b^6/32 - 21*a*b^5*c/16 - 3*a*b^5/8 - 105*a*b^4*c^2/32 - 15*a*b^4*c/8 - 5*a*b^4/8 - 35*a*b^3*c^3/8 - 15*a*b^3*c^2/4 - 5*a*b^3*c/2 - a*b^3 - 105*a*b^2*c^4/32 - 15*a*b^2*c^3/4 - 15*a*b^2*c^2/4 - 3*a*b^2*c - 3*a*b^2/2 - 21*a*b*c^5/16 - 15*a*b*c^4/8 - 5*a*b*c^3/2 - 3*a*b*c^2 - 3*a*b*c - 2*a*b - 7*a*c^6/32 - 3*a*c^5/8 - 5*a*c^4/8 - a*c^3 - 3*a*c^2/2 - 2*a*c - 2*a - b^7/32 - 7*b^6*c/32 - b^6/16 - 21*b^5*c^2/32 - 3*b^5*c/8 - b^5/8 - 35*b^4*c^3/32 - 15*b^4*c^2/16 - 5*b^4*c/8 - b^4/4 - 35*b^3*c^4/32 - 5*b^3*c^3/4 - 5*b^3*c^2/4 - b^3*c - b^3/2 - 21*b^2*c^5/32 - 15*b^2*c^4/16 - 5*b^2*c^3/4 - 3*b^2*c^2/2 - 3*b^2*c/2 - b^2 - 7*b*c^6/32 - 3*b*c^5/8 - 5*b*c^4/8 - b*c^3 - 3*b*c^2/2 - 2*b*c - 2*b - c^7/32 - c^6/16 - c^5/8 - c^4/4 - c^3/2 - c^2 - 2*c - 4) * habc
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2), (a + b) ^ 2 * (a + c) ^ 2 * (b + c) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 8) := @solution
#print axioms solution
