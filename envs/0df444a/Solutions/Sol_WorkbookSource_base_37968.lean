-- Prove2me | solution 1 for WorkbookSource.base_37968
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:33.382964+00:00
-- url     : https://prove2.me/submissions/281b7717-143e-4ea3-ad5b-b321456d7a82

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 4 * (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) ≤ (a + b)^2 * (b + c)^2 * (c + a)^2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^4*b^2 - 2*a^4*b*c + a^4*c^2 - 2*a^3*b^3 + 6*a^3*b^2*c + 6*a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 + 6*a^2*b^3*c + 2*a^2*b^2*c^2 + 6*a^2*b*c^3 + a^2*c^4 - 2*a*b^4*c + 6*a*b^3*c^2 + 6*a*b^2*c^3 - 2*a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^6 + (128 : ℝ) * a^5 * (b - a)^1 + (64 : ℝ) * a^5 * (c - b)^1 + (200 : ℝ) * a^4 * (b - a)^2 + (200 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (40 : ℝ) * a^4 * (c - b)^2 + (152 : ℝ) * a^3 * (b - a)^3 + (228 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (92 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (8 : ℝ) * a^3 * (c - b)^3 + (56 : ℝ) * a^2 * (b - a)^4 + (112 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (68 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (12 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (8 : ℝ) * a^1 * (b - a)^5 + (20 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (16 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (4 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (1 : ℝ) * (b - a)^4 * (c - b)^2 + (2 : ℝ) * (b - a)^3 * (c - b)^3 + (1 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^4*b^2 - 2*a^4*b*c + a^4*c^2 - 2*a^3*b^3 + 6*a^3*b^2*c + 6*a^3*b*c^2 - 2*a^3*c^3 + a^2*b^4 + 6*a^2*b^3*c + 2*a^2*b^2*c^2 + 6*a^2*b*c^3 + a^2*c^4 - 2*a*b^4*c + 6*a*b^3*c^2 + 6*a*b^2*c^3 - 2*a*b*c^4 + b^4*c^2 - 2*b^3*c^3 + b^2*c^4) := by
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
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c), 4 * (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) ≤ (a + b)^2 * (b + c)^2 * (c + a)^2) := @solution
#print axioms solution
