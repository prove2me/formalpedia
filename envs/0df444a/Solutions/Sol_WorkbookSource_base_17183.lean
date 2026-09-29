-- Prove2me | solution 1 for WorkbookSource.base_17183
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:42:42.473683+00:00
-- url     : https://prove2.me/submissions/c95f3388-4188-41db-af74-5e5b4a223492

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 7 * (2 * (a ^ 2 + b ^ 2 + c ^ 2) - 7 * (a * b + b * c + c * a)) ^ 2 ≤ 39 * (a + b + c) ^ 4  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (11*a^4 + 352*a^3*b + 352*a^3*c - 165*a^2*b^2 - 22*a^2*b*c - 165*a^2*c^2 + 352*a*b^3 - 22*a*b^2*c - 22*a*b*c^2 + 352*a*c^3 + 11*b^4 + 352*b^3*c - 165*b^2*c^2 + 352*b*c^3 + 11*c^4) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (1584 : ℝ) * a^4 + (4224 : ℝ) * a^3 * (b - a)^1 + (2112 : ℝ) * a^3 * (c - b)^1 + (4994 : ℝ) * a^2 * (b - a)^2 + (4994 : ℝ) * a^2 * (b - a)^1 * (c - b)^1 + (1826 : ℝ) * a^2 * (c - b)^2 + (2904 : ℝ) * a^1 * (b - a)^3 + (4356 : ℝ) * a^1 * (b - a)^2 * (c - b)^1 + (2948 : ℝ) * a^1 * (b - a)^1 * (c - b)^2 + (748 : ℝ) * a^1 * (c - b)^3 + (561 : ℝ) * (b - a)^4 + (1122 : ℝ) * (b - a)^3 * (c - b)^1 + (957 : ℝ) * (b - a)^2 * (c - b)^2 + (396 : ℝ) * (b - a)^1 * (c - b)^3 + (11 : ℝ) * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (11*a^4 + 352*a^3*b + 352*a^3*c - 165*a^2*b^2 - 22*a^2*b*c - 165*a^2*c^2 + 352*a*b^3 - 22*a*b^2*c - 22*a*b*c^2 + 352*a*c^3 + 11*b^4 + 352*b^3*c - 165*b^2*c^2 + 352*b*c^3 + 11*c^4) := by
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
  nlinarith only [hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 7 * (2 * (a ^ 2 + b ^ 2 + c ^ 2) - 7 * (a * b + b * c + c * a)) ^ 2 ≤ 39 * (a + b + c) ^ 4) := @solution
#print axioms solution
