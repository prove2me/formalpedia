-- Prove2me | solution 1 for WorkbookSource.base_19033
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:42:43.116102+00:00
-- url     : https://prove2.me/submissions/7a68ec70-fbeb-41ae-a7d5-6f90fc21b63f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 4) : (a^2 - a + 1) * (b^2 - b + 1) * (c^2 - c + 1) ≤ 13  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^5*b/256 + 5*a^5*c/256 + a^4*b^2/64 + 21*a^4*b*c/256 + a^4*c^2/64 - a^3*b^3/128 + 35*a^3*b^2*c/128 + 35*a^3*b*c^2/128 - a^3*c^3/128 + a^2*b^4/64 + 35*a^2*b^3*c/128 - 19*a^2*b^2*c^2/64 + 35*a^2*b*c^3/128 + a^2*c^4/64 + 5*a*b^5/256 + 21*a*b^4*c/256 + 35*a*b^3*c^2/128 + 35*a*b^2*c^3/128 + 21*a*b*c^4/256 + 5*a*c^5/256 + 5*b^5*c/256 + b^4*c^2/64 - b^3*c^3/128 + b^2*c^4/64 + 5*b*c^5/256) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (455/256 : ℝ) * a^6 + (455/64 : ℝ) * a^5 * (b - a)^1 + (455/128 : ℝ) * a^5 * (c - b)^1 + (3029/256 : ℝ) * a^4 * (b - a)^2 + (3029/256 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (377/128 : ℝ) * a^4 * (c - b)^2 + (333/32 : ℝ) * a^3 * (b - a)^3 + (999/64 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (509/64 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (11/8 : ℝ) * a^3 * (c - b)^3 + (159/32 : ℝ) * a^2 * (b - a)^4 + (159/16 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (979/128 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (343/128 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (79/256 : ℝ) * a^2 * (c - b)^4 + (9/8 : ℝ) * a^1 * (b - a)^5 + (45/16 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (93/32 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (99/64 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (13/32 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (5/128 : ℝ) * a^1 * (c - b)^5 + (1/16 : ℝ) * (b - a)^6 + (3/16 : ℝ) * (b - a)^5 * (c - b)^1 + (9/32 : ℝ) * (b - a)^4 * (c - b)^2 + (1/4 : ℝ) * (b - a)^3 * (c - b)^3 + (29/256 : ℝ) * (b - a)^2 * (c - b)^4 + (5/256 : ℝ) * (b - a)^1 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^5*b/256 + 5*a^5*c/256 + a^4*b^2/64 + 21*a^4*b*c/256 + a^4*c^2/64 - a^3*b^3/128 + 35*a^3*b^2*c/128 + 35*a^3*b*c^2/128 - a^3*c^3/128 + a^2*b^4/64 + 35*a^2*b^3*c/128 - 19*a^2*b^2*c^2/64 + 35*a^2*b*c^3/128 + a^2*c^4/64 + 5*a*b^5/256 + 21*a*b^4*c/256 + 35*a*b^3*c^2/128 + 35*a*b^2*c^3/128 + 21*a*b*c^4/256 + 5*a*c^5/256 + 5*b^5*c/256 + b^4*c^2/64 - b^3*c^3/128 + b^2*c^4/64 + 5*b*c^5/256) := by
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
  have he : (-a^2*b^2*c^2 + a^2*b^2*c - a^2*b^2 + a^2*b*c^2 - a^2*b*c + a^2*b - a^2*c^2 + a^2*c - a^2 + a*b^2*c^2 - a*b^2*c + a*b^2 - a*b*c^2 + a*b*c - a*b + a*c^2 - a*c + a - b^2*c^2 + b^2*c - b^2 + b*c^2 - b*c + b - c^2 + c + 12) = (5*a^5*b/256 + 5*a^5*c/256 + a^4*b^2/64 + 21*a^4*b*c/256 + a^4*c^2/64 - a^3*b^3/128 + 35*a^3*b^2*c/128 + 35*a^3*b*c^2/128 - a^3*c^3/128 + a^2*b^4/64 + 35*a^2*b^3*c/128 - 19*a^2*b^2*c^2/64 + 35*a^2*b*c^3/128 + a^2*c^4/64 + 5*a*b^5/256 + 21*a*b^4*c/256 + 35*a*b^3*c^2/128 + 35*a*b^2*c^3/128 + 21*a*b*c^4/256 + 5*a*c^5/256 + 5*b^5*c/256 + b^4*c^2/64 - b^3*c^3/128 + b^2*c^4/64 + 5*b*c^5/256) := by
    linear_combination (-5*a^4*b/256 - 5*a^4*c/256 + a^3*b^2/256 - 11*a^3*b*c/256 - 5*a^3*b/64 + a^3*c^2/256 - 5*a^3*c/64 + a^2*b^3/256 - 15*a^2*b^2*c/64 + 3*a^2*b^2/32 - 15*a^2*b*c^2/64 - a^2*b*c/64 - 5*a^2*b/16 + a^2*c^3/256 + 3*a^2*c^2/32 - 5*a^2*c/16 - 5*a*b^4/256 - 11*a*b^3*c/256 - 5*a*b^3/64 - 15*a*b^2*c^2/64 - a*b^2*c/64 - 5*a*b^2/16 - 11*a*b*c^3/256 - a*b*c^2/64 - 7*a*b*c/16 - a*b/4 - 5*a*c^4/256 - 5*a*c^3/64 - 5*a*c^2/16 - a*c/4 - a - 5*b^4*c/256 + b^3*c^2/256 - 5*b^3*c/64 + b^2*c^3/256 + 3*b^2*c^2/32 - 5*b^2*c/16 - 5*b*c^4/256 - 5*b*c^3/64 - 5*b*c^2/16 - b*c/4 - b - c - 3) * habc
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 4), (a^2 - a + 1) * (b^2 - b + 1) * (c^2 - c + 1) ≤ 13) := @solution
#print axioms solution
