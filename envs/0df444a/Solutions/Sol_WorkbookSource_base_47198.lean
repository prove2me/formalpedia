-- Prove2me | solution 1 for WorkbookSource.base_47198
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:17:24.11427+00:00
-- url     : https://prove2.me/submissions/ae4ea118-69be-4ea9-9549-b69e5cd7001f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : 243 * a ^ 2 * b ^ 2 * c ^ 2 + 45 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 4  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^6 + 27*a^4*b^2 - 48*a^4*b*c + 27*a^4*c^2 + 58*a^3*b^3 - 54*a^3*b^2*c - 54*a^3*b*c^2 + 58*a^3*c^3 + 27*a^2*b^4 - 54*a^2*b^3*c + 126*a^2*b^2*c^2 - 54*a^2*b*c^3 + 27*a^2*c^4 - 48*a*b^4*c - 54*a*b^3*c^2 - 54*a*b^2*c^3 - 48*a*b*c^4 + 2*b^6 + 27*b^4*c^2 + 58*b^3*c^3 + 27*b^2*c^4 + 2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (162 : ℝ) * a^4 * (b - a)^2 + (162 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (162 : ℝ) * a^4 * (c - b)^2 + (576 : ℝ) * a^3 * (b - a)^3 + (864 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (432 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (72 : ℝ) * a^3 * (c - b)^3 + (792 : ℝ) * a^2 * (b - a)^4 + (1584 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (972 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (180 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (36 : ℝ) * a^2 * (c - b)^4 + (492 : ℝ) * a^1 * (b - a)^5 + (1230 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (1068 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (372 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (66 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (12 : ℝ) * a^1 * (c - b)^5 + (116 : ℝ) * (b - a)^6 + (348 : ℝ) * (b - a)^5 * (c - b)^1 + (393 : ℝ) * (b - a)^4 * (c - b)^2 + (206 : ℝ) * (b - a)^3 * (c - b)^3 + (57 : ℝ) * (b - a)^2 * (c - b)^4 + (12 : ℝ) * (b - a)^1 * (c - b)^5 + (2 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^6 + 27*a^4*b^2 - 48*a^4*b*c + 27*a^4*c^2 + 58*a^3*b^3 - 54*a^3*b^2*c - 54*a^3*b*c^2 + 58*a^3*c^3 + 27*a^2*b^4 - 54*a^2*b^3*c + 126*a^2*b^2*c^2 - 54*a^2*b*c^3 + 27*a^2*c^4 - 48*a*b^4*c - 54*a*b^3*c^2 - 54*a*b^2*c^3 - 48*a*b*c^4 + 2*b^6 + 27*b^4*c^2 + 58*b^3*c^3 + 27*b^2*c^4 + 2*c^6) := by
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
  have he : (243*a^2*b^2*c^2 + 45*a^2*b^2 + 45*a^2*c^2 + 6*a^2 + 45*b^2*c^2 + 6*b^2 + 6*c^2 - 4) = (2*a^6 + 27*a^4*b^2 - 48*a^4*b*c + 27*a^4*c^2 + 58*a^3*b^3 - 54*a^3*b^2*c - 54*a^3*b*c^2 + 58*a^3*c^3 + 27*a^2*b^4 - 54*a^2*b^3*c + 126*a^2*b^2*c^2 - 54*a^2*b*c^3 + 27*a^2*c^4 - 48*a*b^4*c - 54*a*b^3*c^2 - 54*a*b^2*c^3 - 48*a*b*c^4 + 2*b^6 + 27*b^4*c^2 + 58*b^3*c^3 + 27*b^2*c^4 + 2*c^6) := by
    linear_combination (-2*a^5 + 2*a^4*b + 2*a^4*c - 2*a^4 - 29*a^3*b^2 + 44*a^3*b*c + 4*a^3*b - 29*a^3*c^2 + 4*a^3*c - 2*a^3 - 29*a^2*b^3 + 39*a^2*b^2*c - 33*a^2*b^2 + 39*a^2*b*c^2 + 36*a^2*b*c + 6*a^2*b - 29*a^2*c^3 - 33*a^2*c^2 + 6*a^2*c - 2*a^2 + 2*a*b^4 + 44*a*b^3*c + 4*a*b^3 + 39*a*b^2*c^2 + 36*a*b^2*c + 6*a*b^2 + 44*a*b*c^3 + 36*a*b*c^2 + 24*a*b*c + 8*a*b + 2*a*c^4 + 4*a*c^3 + 6*a*c^2 + 8*a*c + 4*a - 2*b^5 + 2*b^4*c - 2*b^4 - 29*b^3*c^2 + 4*b^3*c - 2*b^3 - 29*b^2*c^3 - 33*b^2*c^2 + 6*b^2*c - 2*b^2 + 2*b*c^4 + 4*b*c^3 + 6*b*c^2 + 8*b*c + 4*b - 2*c^5 - 2*c^4 - 2*c^3 - 2*c^2 + 4*c + 4) * hab
  nlinarith only [hp, he]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1), 243 * a ^ 2 * b ^ 2 * c ^ 2 + 45 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 4) := @solution
#print axioms solution
