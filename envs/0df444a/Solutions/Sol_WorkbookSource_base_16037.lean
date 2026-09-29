-- Prove2me | solution 1 for WorkbookSource.base_16037
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:07.676227+00:00
-- url     : https://prove2.me/submissions/2b3b8b08-41ea-4448-aca1-df5386108893

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 * (-a + b + c) * (a - b + c) * (a + b - c) ≤ 27 * a ^ 2 * b ^ 2 * c ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - a^4*b^2 + 2*a^4*b*c - a^4*c^2 - 4*a^3*b^3 - 4*a^3*b^2*c - 4*a^3*b*c^2 - 4*a^3*c^3 - a^2*b^4 - 4*a^2*b^3*c + 21*a^2*b^2*c^2 - 4*a^2*b*c^3 - a^2*c^4 + 2*a*b^5 + 2*a*b^4*c - 4*a*b^3*c^2 - 4*a*b^2*c^3 + 2*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c - b^4*c^2 - 4*b^3*c^3 - b^2*c^4 + 2*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (18 : ℝ) * a^4 * (b - a)^2 + (18 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (18 : ℝ) * a^4 * (c - b)^2 + (28 : ℝ) * a^3 * (b - a)^3 + (42 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (102 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (44 : ℝ) * a^3 * (c - b)^3 + (11 : ℝ) * a^2 * (b - a)^4 + (22 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (147 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (136 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (35 : ℝ) * a^2 * (c - b)^4 + (80 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (120 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (60 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^4 * (c - b)^2 + (32 : ℝ) * (b - a)^3 * (c - b)^3 + (24 : ℝ) * (b - a)^2 * (c - b)^4 + (8 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - a^4*b^2 + 2*a^4*b*c - a^4*c^2 - 4*a^3*b^3 - 4*a^3*b^2*c - 4*a^3*b*c^2 - 4*a^3*c^3 - a^2*b^4 - 4*a^2*b^3*c + 21*a^2*b^2*c^2 - 4*a^2*b*c^3 - a^2*c^4 + 2*a*b^5 + 2*a*b^4*c - 4*a*b^3*c^2 - 4*a*b^2*c^3 + 2*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c - b^4*c^2 - 4*b^3*c^3 - b^2*c^4 + 2*b*c^5 + c^6) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) ^ 3 * (-a + b + c) * (a - b + c) * (a + b - c) ≤ 27 * a ^ 2 * b ^ 2 * c ^ 2) := @solution
#print axioms solution
