-- Prove2me | solution 1 for WorkbookSource.plus_68139
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:44:13.786405+00:00
-- url     : https://prove2.me/submissions/afa3f481-3896-41eb-93fb-9d8dae33bc40

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 5 * (a + b + c) ^ 6 ≥ 27 * (a * b + a * c + b * c) * (11 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) + 4 * a * b * c * (a + b + c))   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6 + 30*a^5*b + 30*a^5*c + 75*a^4*b^2 + 150*a^4*b*c + 75*a^4*c^2 - 197*a^3*b^3 - 105*a^3*b^2*c - 105*a^3*b*c^2 - 197*a^3*c^3 + 75*a^2*b^4 - 105*a^2*b^3*c + 126*a^2*b^2*c^2 - 105*a^2*b*c^3 + 75*a^2*c^4 + 30*a*b^5 + 150*a*b^4*c - 105*a*b^3*c^2 - 105*a*b^2*c^3 + 150*a*b*c^4 + 30*a*c^5 + 5*b^6 + 30*b^5*c + 75*b^4*c^2 - 197*b^3*c^3 + 75*b^2*c^4 + 30*b*c^5 + 5*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (729 : ℝ) * a^4 * (b - a)^2 + (729 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (729 : ℝ) * a^4 * (c - b)^2 + (1620 : ℝ) * a^3 * (b - a)^3 + (2430 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (3402 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (1296 : ℝ) * a^3 * (c - b)^3 + (1161 : ℝ) * a^2 * (b - a)^4 + (2322 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (4455 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (3294 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (675 : ℝ) * a^2 * (c - b)^4 + (288 : ℝ) * a^1 * (b - a)^5 + (720 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (2016 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (2304 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (900 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (90 : ℝ) * a^1 * (c - b)^5 + (23 : ℝ) * (b - a)^6 + (69 : ℝ) * (b - a)^5 * (c - b)^1 + (309 : ℝ) * (b - a)^4 * (c - b)^2 + (503 : ℝ) * (b - a)^3 * (c - b)^3 + (300 : ℝ) * (b - a)^2 * (c - b)^4 + (60 : ℝ) * (b - a)^1 * (c - b)^5 + (5 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6 + 30*a^5*b + 30*a^5*c + 75*a^4*b^2 + 150*a^4*b*c + 75*a^4*c^2 - 197*a^3*b^3 - 105*a^3*b^2*c - 105*a^3*b*c^2 - 197*a^3*c^3 + 75*a^2*b^4 - 105*a^2*b^3*c + 126*a^2*b^2*c^2 - 105*a^2*b*c^3 + 75*a^2*c^4 + 30*a*b^5 + 150*a*b^4*c - 105*a*b^3*c^2 - 105*a*b^2*c^3 + 150*a*b*c^4 + 30*a*c^5 + 5*b^6 + 30*b^5*c + 75*b^4*c^2 - 197*b^3*c^3 + 75*b^2*c^4 + 30*b*c^5 + 5*c^6) := by
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
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 5 * (a + b + c) ^ 6 ≥ 27 * (a * b + a * c + b * c) * (11 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) + 4 * a * b * c * (a + b + c))) := @solution
#print axioms solution
