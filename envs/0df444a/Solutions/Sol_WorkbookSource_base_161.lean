-- Prove2me | solution 1 for WorkbookSource.base_161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:35:01.496731+00:00
-- url     : https://prove2.me/submissions/230b9777-4737-4df5-ac93-0acb0c4bedf8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2 + 4 * (a * b + b * c + c * a)) / (2 * a * b * c) ≥ (9 * (a + b + c)) / (2 * (a * b + b * c + c * a)) + 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^5*b^2 + 2*a^5*b*c + a^5*c^2 + 5*a^4*b^3 + 3*a^4*b^2*c + 3*a^4*b*c^2 + 5*a^4*c^3 + 5*a^3*b^4 - 2*a^3*b^3*c - 18*a^3*b^2*c^2 - 2*a^3*b*c^3 + 5*a^3*c^4 + a^2*b^5 + 3*a^2*b^4*c - 18*a^2*b^3*c^2 - 18*a^2*b^2*c^3 + 3*a^2*b*c^4 + a^2*c^5 + 2*a*b^5*c + 3*a*b^4*c^2 - 2*a*b^3*c^3 + 3*a*b^2*c^4 + 2*a*b*c^5 + b^5*c^2 + 5*b^4*c^3 + 5*b^3*c^4 + b^2*c^5) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (72 : ℝ) * a^5 * (b - a)^2 + (72 : ℝ) * a^5 * (b - a)^1 * (c - b)^1 + (72 : ℝ) * a^5 * (c - b)^2 + (268 : ℝ) * a^4 * (b - a)^3 + (402 : ℝ) * a^4 * (b - a)^2 * (c - b)^1 + (318 : ℝ) * a^4 * (b - a)^1 * (c - b)^2 + (92 : ℝ) * a^4 * (c - b)^3 + (388 : ℝ) * a^3 * (b - a)^4 + (776 : ℝ) * a^3 * (b - a)^3 * (c - b)^1 + (644 : ℝ) * a^3 * (b - a)^2 * (c - b)^2 + (256 : ℝ) * a^3 * (b - a)^1 * (c - b)^3 + (36 : ℝ) * a^3 * (c - b)^4 + (272 : ℝ) * a^2 * (b - a)^5 + (680 : ℝ) * a^2 * (b - a)^4 * (c - b)^1 + (656 : ℝ) * a^2 * (b - a)^3 * (c - b)^2 + (304 : ℝ) * a^2 * (b - a)^2 * (c - b)^3 + (64 : ℝ) * a^2 * (b - a)^1 * (c - b)^4 + (4 : ℝ) * a^2 * (c - b)^5 + (92 : ℝ) * a^1 * (b - a)^6 + (276 : ℝ) * a^1 * (b - a)^5 * (c - b)^1 + (315 : ℝ) * a^1 * (b - a)^4 * (c - b)^2 + (170 : ℝ) * a^1 * (b - a)^3 * (c - b)^3 + (43 : ℝ) * a^1 * (b - a)^2 * (c - b)^4 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^5 + (12 : ℝ) * (b - a)^7 + (42 : ℝ) * (b - a)^6 * (c - b)^1 + (56 : ℝ) * (b - a)^5 * (c - b)^2 + (35 : ℝ) * (b - a)^4 * (c - b)^3 + (10 : ℝ) * (b - a)^3 * (c - b)^4 + (1 : ℝ) * (b - a)^2 * (c - b)^5 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^5*b^2 + 2*a^5*b*c + a^5*c^2 + 5*a^4*b^3 + 3*a^4*b^2*c + 3*a^4*b*c^2 + 5*a^4*c^3 + 5*a^3*b^4 - 2*a^3*b^3*c - 18*a^3*b^2*c^2 - 2*a^3*b*c^3 + 5*a^3*c^4 + a^2*b^5 + 3*a^2*b^4*c - 18*a^2*b^3*c^2 - 18*a^2*b^2*c^3 + 3*a^2*b*c^4 + a^2*c^5 + 2*a*b^5*c + 3*a*b^4*c^2 - 2*a*b^3*c^3 + 3*a*b^2*c^4 + 2*a*b*c^5 + b^5*c^2 + 5*b^4*c^3 + 5*b^3*c^4 + b^2*c^5) := by
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
  have hn : 0 ≤ (a^5*b^2 + 2*a^5*b*c + a^5*c^2 + 5*a^4*b^3 + 3*a^4*b^2*c + 3*a^4*b*c^2 + 5*a^4*c^3 + 5*a^3*b^4 - 2*a^3*b^3*c - 18*a^3*b^2*c^2 - 2*a^3*b*c^3 + 5*a^3*c^4 + a^2*b^5 + 3*a^2*b^4*c - 18*a^2*b^3*c^2 - 18*a^2*b^2*c^3 + 3*a^2*b*c^4 + a^2*c^5 + 2*a*b^5*c + 3*a*b^4*c^2 - 2*a*b^3*c^3 + 3*a*b^2*c^4 + 2*a*b*c^5 + b^5*c^2 + 5*b^4*c^3 + 5*b^3*c^4 + b^2*c^5) := by nlinarith only [hp]
  have hd : 0 < (2*a*b*c*(a + b)*(a + c)*(b + c)*(a*b + a*c + b*c) : ℝ) := by positivity
  have herat : ( (a^2 + b^2 + c^2 + 4 * (a * b + b * c + c * a)) / (2 * a * b * c) ) - ( (9 * (a + b + c)) / (2 * (a * b + b * c + c * a)) + 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))  ) = (a^5*b^2 + 2*a^5*b*c + a^5*c^2 + 5*a^4*b^3 + 3*a^4*b^2*c + 3*a^4*b*c^2 + 5*a^4*c^3 + 5*a^3*b^4 - 2*a^3*b^3*c - 18*a^3*b^2*c^2 - 2*a^3*b*c^3 + 5*a^3*c^4 + a^2*b^5 + 3*a^2*b^4*c - 18*a^2*b^3*c^2 - 18*a^2*b^2*c^3 + 3*a^2*b*c^4 + a^2*c^5 + 2*a*b^5*c + 3*a*b^4*c^2 - 2*a*b^3*c^3 + 3*a*b^2*c^4 + 2*a*b*c^5 + b^5*c^2 + 5*b^4*c^3 + 5*b^3*c^4 + b^2*c^5) / (2*a*b*c*(a + b)*(a + c)*(b + c)*(a*b + a*c + b*c)) := by
    field_simp (disch := positivity)
    <;> ring
  have hrat := div_nonneg hn (le_of_lt hd)
  rw [← herat] at hrat
  linarith only [hrat]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a^2 + b^2 + c^2 + 4 * (a * b + b * c + c * a)) / (2 * a * b * c) ≥ (9 * (a + b + c)) / (2 * (a * b + b * c + c * a)) + 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a))) := @solution
#print axioms solution
