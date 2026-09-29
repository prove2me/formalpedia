-- Prove2me | solution 1 for WorkbookSource.base_42124
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:13:21.127878+00:00
-- url     : https://prove2.me/submissions/b77ff9bd-e1be-4590-8d53-7075448d87c5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : a^2 + b^2 + c^2 ≥ 2 * (a^3 * b^3 + a^3 * c^3 + c^3 * b^3) + 9 * a^2 * b^2 * c^2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6/16 + a^5*b/4 + a^5*c/4 + 7*a^4*b^2/16 + 3*a^4*b*c/4 + 7*a^4*c^2/16 - 3*a^3*b^3/2 + a^3*b^2*c + a^3*b*c^2 - 3*a^3*c^3/2 + 7*a^2*b^4/16 + a^2*b^3*c - 63*a^2*b^2*c^2/8 + a^2*b*c^3 + 7*a^2*c^4/16 + a*b^5/4 + 3*a*b^4*c/4 + a*b^3*c^2 + a*b^2*c^3 + 3*a*b*c^4/4 + a*c^5/4 + b^6/16 + b^5*c/4 + 7*b^4*c^2/16 - 3*b^3*c^3/2 + 7*b^2*c^4/16 + b*c^5/4 + c^6/16) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (3/16 : ℝ) * a^6 + (3/4 : ℝ) * a^5 * (b - a)^1 + (3/8 : ℝ) * a^5 * (c - b)^1 + (69/8 : ℝ) * a^4 * (b - a)^2 + (69/8 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (123/16 : ℝ) * a^4 * (c - b)^2 + (19 : ℝ) * a^3 * (b - a)^3 + (57/2 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (33 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (47/4 : ℝ) * a^3 * (c - b)^3 + (15 : ℝ) * a^2 * (b - a)^4 + (30 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (171/4 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (111/4 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (81/16 : ℝ) * a^2 * (c - b)^4 + (4 : ℝ) * a^1 * (b - a)^5 + (10 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (19 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (37/2 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (29/4 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (7/8 : ℝ) * a^1 * (c - b)^5 + (2 : ℝ) * (b - a)^4 * (c - b)^2 + (4 : ℝ) * (b - a)^3 * (c - b)^3 + (21/8 : ℝ) * (b - a)^2 * (c - b)^4 + (5/8 : ℝ) * (b - a)^1 * (c - b)^5 + (1/16 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6/16 + a^5*b/4 + a^5*c/4 + 7*a^4*b^2/16 + 3*a^4*b*c/4 + 7*a^4*c^2/16 - 3*a^3*b^3/2 + a^3*b^2*c + a^3*b*c^2 - 3*a^3*c^3/2 + 7*a^2*b^4/16 + a^2*b^3*c - 63*a^2*b^2*c^2/8 + a^2*b*c^3 + 7*a^2*c^4/16 + a*b^5/4 + 3*a*b^4*c/4 + a*b^3*c^2 + a*b^2*c^3 + 3*a*b*c^4/4 + a*c^5/4 + b^6/16 + b^5*c/4 + 7*b^4*c^2/16 - 3*b^3*c^3/2 + 7*b^2*c^4/16 + b*c^5/4 + c^6/16) := by
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
  have he : (-2*a^3*b^3 - 2*a^3*c^3 - 9*a^2*b^2*c^2 + a^2 - 2*b^3*c^3 + b^2 + c^2) = (a^6/16 + a^5*b/4 + a^5*c/4 + 7*a^4*b^2/16 + 3*a^4*b*c/4 + 7*a^4*c^2/16 - 3*a^3*b^3/2 + a^3*b^2*c + a^3*b*c^2 - 3*a^3*c^3/2 + 7*a^2*b^4/16 + a^2*b^3*c - 63*a^2*b^2*c^2/8 + a^2*b*c^3 + 7*a^2*c^4/16 + a*b^5/4 + 3*a*b^4*c/4 + a*b^3*c^2 + a*b^2*c^3 + 3*a*b*c^4/4 + a*c^5/4 + b^6/16 + b^5*c/4 + 7*b^4*c^2/16 - 3*b^3*c^3/2 + 7*b^2*c^4/16 + b*c^5/4 + c^6/16) := by
    linear_combination (-a^5/16 - 3*a^4*b/16 - 3*a^4*c/16 - a^4/8 - a^3*b^2/4 - 3*a^3*b*c/8 - a^3*b/4 - a^3*c^2/4 - a^3*c/4 - a^3/4 - a^2*b^3/4 - 3*a^2*b^2*c/8 - a^2*b^2/4 - 3*a^2*b*c^2/8 - a^2*b*c/4 - a^2*b/4 - a^2*c^3/4 - a^2*c^2/4 - a^2*c/4 - a^2/2 - 3*a*b^4/16 - 3*a*b^3*c/8 - a*b^3/4 - 3*a*b^2*c^2/8 - a*b^2*c/4 - a*b^2/4 - 3*a*b*c^3/8 - a*b*c^2/4 - 3*a*c^4/16 - a*c^3/4 - a*c^2/4 - b^5/16 - 3*b^4*c/16 - b^4/8 - b^3*c^2/4 - b^3*c/4 - b^3/4 - b^2*c^3/4 - b^2*c^2/4 - b^2*c/4 - b^2/2 - 3*b*c^4/16 - b*c^3/4 - b*c^2/4 - c^5/16 - c^4/8 - c^3/4 - c^2/2) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2), a^2 + b^2 + c^2 ≥ 2 * (a^3 * b^3 + a^3 * c^3 + c^3 * b^3) + 9 * a^2 * b^2 * c^2) := @solution
#print axioms solution
