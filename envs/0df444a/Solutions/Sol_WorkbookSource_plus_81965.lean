-- Prove2me | solution 1 for WorkbookSource.plus_81965
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:57:30.046302+00:00
-- url     : https://prove2.me/submissions/9a805457-b75e-4f54-a39e-dc23ee47dc40

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (1 / (2 * a + b * c) + 1 / (2 * b + c * a) + 1 / (2 * c + a * b)) ≤ (3 / (b * c + c * a + a * b))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (2*a^4*b^2/9 + 2*a^4*b*c/3 + 2*a^4*c^2/9 + 4*a^3*b^3/9 - 5*a^3*b^2*c/9 - 5*a^3*b*c^2/9 + 4*a^3*c^3/9 + 2*a^2*b^4/9 - 5*a^2*b^3*c/9 - 4*a^2*b^2*c^2/3 - 5*a^2*b*c^3/9 + 2*a^2*c^4/9 + 2*a*b^4*c/3 - 5*a*b^3*c^2/9 - 5*a*b^2*c^3/9 + 2*a*b*c^4/3 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 2*b^2*c^4/9) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (4 : ℝ) * a^4 * (b - a)^2 + (4 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (4 : ℝ) * a^4 * (c - b)^2 + (106/9 : ℝ) * a^3 * (b - a)^3 + (53/3 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (43/3 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (38/9 : ℝ) * a^3 * (c - b)^3 + (112/9 : ℝ) * a^2 * (b - a)^4 + (224/9 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (21 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (77/9 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (10/9 : ℝ) * a^2 * (c - b)^4 + (50/9 : ℝ) * a^1 * (b - a)^5 + (125/9 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (40/3 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (55/9 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (10/9 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (8/9 : ℝ) * (b - a)^6 + (8/3 : ℝ) * (b - a)^5 * (c - b)^1 + (26/9 : ℝ) * (b - a)^4 * (c - b)^2 + (4/3 : ℝ) * (b - a)^3 * (c - b)^3 + (2/9 : ℝ) * (b - a)^2 * (c - b)^4 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (2*a^4*b^2/9 + 2*a^4*b*c/3 + 2*a^4*c^2/9 + 4*a^3*b^3/9 - 5*a^3*b^2*c/9 - 5*a^3*b*c^2/9 + 4*a^3*c^3/9 + 2*a^2*b^4/9 - 5*a^2*b^3*c/9 - 4*a^2*b^2*c^2/3 - 5*a^2*b*c^3/9 + 2*a^2*c^4/9 + 2*a*b^4*c/3 - 5*a*b^3*c^2/9 - 5*a*b^2*c^3/9 + 2*a*b*c^4/3 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 2*b^2*c^4/9) := by
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
  have he : (-a^3*b^2*c - 2*a^3*b^2 - a^3*b*c^2 + 2*a^3*b*c - 2*a^3*c^2 - a^2*b^3*c - 2*a^2*b^3 - 4*a^2*b^2*c + 8*a^2*b^2 - a^2*b*c^3 - 4*a^2*b*c^2 - 8*a^2*b*c - 2*a^2*c^3 + 8*a^2*c^2 - a*b^3*c^2 + 2*a*b^3*c - a*b^2*c^3 - 4*a*b^2*c^2 - 8*a*b^2*c + 2*a*b*c^3 - 8*a*b*c^2 + 24*a*b*c - 2*b^3*c^2 - 2*b^2*c^3 + 8*b^2*c^2) = (2*a^4*b^2/9 + 2*a^4*b*c/3 + 2*a^4*c^2/9 + 4*a^3*b^3/9 - 5*a^3*b^2*c/9 - 5*a^3*b*c^2/9 + 4*a^3*c^3/9 + 2*a^2*b^4/9 - 5*a^2*b^3*c/9 - 4*a^2*b^2*c^2/3 - 5*a^2*b*c^3/9 + 2*a^2*c^4/9 + 2*a*b^4*c/3 - 5*a*b^3*c^2/9 - 5*a*b^2*c^3/9 + 2*a*b*c^4/3 + 2*b^4*c^2/9 + 4*b^3*c^3/9 + 2*b^2*c^4/9) := by
    linear_combination (-2*a^3*b^2/9 - 2*a^3*b*c/3 - 2*a^3*c^2/9 - 2*a^2*b^3/9 + 4*a^2*b^2*c/9 - 8*a^2*b^2/3 + 4*a^2*b*c^2/9 - 2*a^2*c^3/9 - 8*a^2*c^2/3 - 2*a*b^3*c/3 + 4*a*b^2*c^2/9 - 2*a*b*c^3/3 - 8*a*b*c - 2*b^3*c^2/9 - 2*b^2*c^3/9 - 8*b^2*c^2/3) * hab
  have hn : 0 ≤ (-a^3*b^2*c - 2*a^3*b^2 - a^3*b*c^2 + 2*a^3*b*c - 2*a^3*c^2 - a^2*b^3*c - 2*a^2*b^3 - 4*a^2*b^2*c + 8*a^2*b^2 - a^2*b*c^3 - 4*a^2*b*c^2 - 8*a^2*b*c - 2*a^2*c^3 + 8*a^2*c^2 - a*b^3*c^2 + 2*a*b^3*c - a*b^2*c^3 - 4*a*b^2*c^2 - 8*a*b^2*c + 2*a*b*c^3 - 8*a*b*c^2 + 24*a*b*c - 2*b^3*c^2 - 2*b^2*c^3 + 8*b^2*c^2) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), (1 / (2 * a + b * c) + 1 / (2 * b + c * a) + 1 / (2 * c + a * b)) ≤ (3 / (b * c + c * a + a * b))) := @solution
#print axioms solution
