-- Prove2me | solution 1 for WorkbookSource.base_4034
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:03:27.644524+00:00
-- url     : https://prove2.me/submissions/2a8a91de-d8eb-4958-8dc5-807402519339

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 2) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a * b * c ≤ 1  := by
  have hp : 0 ≤ (a^4/16 + a^3*b/4 + a^3*c/4 - 5*a^2*b^2/8 + a^2*b*c/4 - 5*a^2*c^2/8 + a*b^3/4 + a*b^2*c/4 + a*b*c^2/4 + a*c^3/4 + b^4/16 + b^3*c/4 - 5*b^2*c^2/8 + b*c^3/4 + c^4/16) := by
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (b - a) := by linarith
        have hdiff2 : 0 ≤ (c - b) := by linarith
        have hpos : 0 ≤ (9/16 : ℝ) * a^4 + (3/2 : ℝ) * a^3 * (b - a)^1 + (3/4 : ℝ) * a^3 * (c - b)^1 + (2 : ℝ) * a^2 * (b - a)^2 + (2 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (7/8 : ℝ) * a^2 * (c - b)^2 + (1 : ℝ) * a^1 * (b - a)^3 + (3/2 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (2 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (3/4 : ℝ) * a^1 * (c - b)^3 + (1/2 : ℝ) * (b - a)^2 * (c - b)^2 + (1/2 : ℝ) * (b - a)^1 * (c - b)^3 + (1/16 : ℝ) * (c - b)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total a c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - a) := by linarith
          have hdiff2 : 0 ≤ (b - c) := by linarith
          have hpos : 0 ≤ (9/16 : ℝ) * a^4 + (3/2 : ℝ) * a^3 * (c - a)^1 + (3/4 : ℝ) * a^3 * (b - c)^1 + (2 : ℝ) * a^2 * (c - a)^2 + (2 : ℝ) * a^2 * (c - a)^1 * (b - c)^1 + (7/8 : ℝ) * a^2 * (b - c)^2 + (1 : ℝ) * a^1 * (c - a)^3 + (3/2 : ℝ) * a^1 * (c - a)^2 * (b - c)^1 + (2 : ℝ) * a^1 * (c - a)^1 * (b - c)^2 + (3/4 : ℝ) * a^1 * (b - c)^3 + (1/2 : ℝ) * (c - a)^2 * (b - c)^2 + (1/2 : ℝ) * (c - a)^1 * (b - c)^3 + (1/16 : ℝ) * (b - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (a - c) := by linarith
          have hdiff2 : 0 ≤ (b - a) := by linarith
          have hpos : 0 ≤ (9/16 : ℝ) * c^4 + (3/2 : ℝ) * c^3 * (a - c)^1 + (3/4 : ℝ) * c^3 * (b - a)^1 + (2 : ℝ) * c^2 * (a - c)^2 + (2 : ℝ) * c^2 * (a - c)^1 * (b - a)^1 + (7/8 : ℝ) * c^2 * (b - a)^2 + (1 : ℝ) * c^1 * (a - c)^3 + (3/2 : ℝ) * c^1 * (a - c)^2 * (b - a)^1 + (2 : ℝ) * c^1 * (a - c)^1 * (b - a)^2 + (3/4 : ℝ) * c^1 * (b - a)^3 + (1/2 : ℝ) * (a - c)^2 * (b - a)^2 + (1/2 : ℝ) * (a - c)^1 * (b - a)^3 + (1/16 : ℝ) * (b - a)^4 := by positivity
          convert hpos using 1 <;> ring
    · rcases le_total a c with hbc | hcb
      ·
        have hdiff1 : 0 ≤ (a - b) := by linarith
        have hdiff2 : 0 ≤ (c - a) := by linarith
        have hpos : 0 ≤ (9/16 : ℝ) * b^4 + (3/2 : ℝ) * b^3 * (a - b)^1 + (3/4 : ℝ) * b^3 * (c - a)^1 + (2 : ℝ) * b^2 * (a - b)^2 + (2 : ℝ) * b^2 * (a - b)^1 * (c - a)^1 + (7/8 : ℝ) * b^2 * (c - a)^2 + (1 : ℝ) * b^1 * (a - b)^3 + (3/2 : ℝ) * b^1 * (a - b)^2 * (c - a)^1 + (2 : ℝ) * b^1 * (a - b)^1 * (c - a)^2 + (3/4 : ℝ) * b^1 * (c - a)^3 + (1/2 : ℝ) * (a - b)^2 * (c - a)^2 + (1/2 : ℝ) * (a - b)^1 * (c - a)^3 + (1/16 : ℝ) * (c - a)^4 := by positivity
        convert hpos using 1 <;> ring
      · rcases le_total b c with hac | hca
        ·
          have hdiff1 : 0 ≤ (c - b) := by linarith
          have hdiff2 : 0 ≤ (a - c) := by linarith
          have hpos : 0 ≤ (9/16 : ℝ) * b^4 + (3/2 : ℝ) * b^3 * (c - b)^1 + (3/4 : ℝ) * b^3 * (a - c)^1 + (2 : ℝ) * b^2 * (c - b)^2 + (2 : ℝ) * b^2 * (c - b)^1 * (a - c)^1 + (7/8 : ℝ) * b^2 * (a - c)^2 + (1 : ℝ) * b^1 * (c - b)^3 + (3/2 : ℝ) * b^1 * (c - b)^2 * (a - c)^1 + (2 : ℝ) * b^1 * (c - b)^1 * (a - c)^2 + (3/4 : ℝ) * b^1 * (a - c)^3 + (1/2 : ℝ) * (c - b)^2 * (a - c)^2 + (1/2 : ℝ) * (c - b)^1 * (a - c)^3 + (1/16 : ℝ) * (a - c)^4 := by positivity
          convert hpos using 1 <;> ring
        ·
          have hdiff1 : 0 ≤ (b - c) := by linarith
          have hdiff2 : 0 ≤ (a - b) := by linarith
          have hpos : 0 ≤ (9/16 : ℝ) * c^4 + (3/2 : ℝ) * c^3 * (b - c)^1 + (3/4 : ℝ) * c^3 * (a - b)^1 + (2 : ℝ) * c^2 * (b - c)^2 + (2 : ℝ) * c^2 * (b - c)^1 * (a - b)^1 + (7/8 : ℝ) * c^2 * (a - b)^2 + (1 : ℝ) * c^1 * (b - c)^3 + (3/2 : ℝ) * c^1 * (b - c)^2 * (a - b)^1 + (2 : ℝ) * c^1 * (b - c)^1 * (a - b)^2 + (3/4 : ℝ) * c^1 * (a - b)^3 + (1/2 : ℝ) * (b - c)^2 * (a - b)^2 + (1/2 : ℝ) * (b - c)^1 * (a - b)^3 + (1/16 : ℝ) * (a - b)^4 := by positivity
          convert hpos using 1 <;> ring
  have he : (-a^2*b^2 - a^2*c^2 - a*b*c - b^2*c^2 + 1) = (a^4/16 + a^3*b/4 + a^3*c/4 - 5*a^2*b^2/8 + a^2*b*c/4 - 5*a^2*c^2/8 + a*b^3/4 + a*b^2*c/4 + a*b*c^2/4 + a*c^3/4 + b^4/16 + b^3*c/4 - 5*b^2*c^2/8 + b*c^3/4 + c^4/16) := by
    linear_combination (-a^3/16 - 3*a^2*b/16 - 3*a^2*c/16 - a^2/8 - 3*a*b^2/16 + a*b*c/8 - a*b/4 - 3*a*c^2/16 - a*c/4 - a/4 - b^3/16 - 3*b^2*c/16 - b^2/8 - 3*b*c^2/16 - b*c/4 - b/4 - c^3/16 - c^2/8 - c/4 - 1/2) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 2), a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a * b * c ≤ 1) := @solution
#print axioms solution
