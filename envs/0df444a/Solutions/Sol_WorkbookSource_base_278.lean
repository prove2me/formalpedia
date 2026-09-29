-- Prove2me | solution 1 for WorkbookSource.base_278
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:40.282508+00:00
-- url     : https://prove2.me/submissions/c174b6f4-6d06-4562-bcaa-8b5a99b11223

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a)) * (b / (c + a) + c / (a + b)) * (c / (a + b) + a / (b + c)) ≥ 7 / 8 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + 1 / 8  := by
  have haux (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b^2 + 2*a^6*b*c + a^6*c^2 + a^5*b^3 - 5*a^5*b^2*c - 5*a^5*b*c^2 + a^5*c^3 + 7*a^4*b^3*c - 2*a^4*b^2*c^2 + 7*a^4*b*c^3 + a^3*b^5 + 7*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 + 7*a^3*b*c^4 + a^3*c^5 + a^2*b^6 - 5*a^2*b^5*c - 2*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 2*a^2*b^2*c^4 - 5*a^2*b*c^5 + a^2*c^6 + 2*a*b^6*c - 5*a*b^5*c^2 + 7*a*b^4*c^3 + 7*a*b^3*c^4 - 5*a*b^2*c^5 + 2*a*b*c^6 + b^6*c^2 + b^5*c^3 + b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (32 : ℝ) * a^6 * (b - a)^2 + (32 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (32 : ℝ) * a^6 * (c - b)^2 + (144 : ℝ) * a^5 * (b - a)^3 + (216 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (168 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (48 : ℝ) * a^5 * (c - b)^3 + (272 : ℝ) * a^4 * (b - a)^4 + (544 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (456 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (184 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (32 : ℝ) * a^4 * (c - b)^4 + (272 : ℝ) * a^3 * (b - a)^5 + (680 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (688 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (352 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (104 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (16 : ℝ) * a^3 * (c - b)^5 + (148 : ℝ) * a^2 * (b - a)^6 + (444 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (552 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (364 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (144 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (36 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (4 : ℝ) * a^2 * (c - b)^6 + (40 : ℝ) * a^1 * (b - a)^7 + (140 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (212 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (180 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (92 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (28 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (4 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (b - a)^8 + (16 : ℝ) * (b - a)^7 * (c - b)^1 + (29 : ℝ) * (b - a)^6 * (c - b)^2 + (31 : ℝ) * (b - a)^5 * (c - b)^3 + (20 : ℝ) * (b - a)^4 * (c - b)^4 + (7 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b^2 + 2*a^6*b*c + a^6*c^2 + a^5*b^3 - 5*a^5*b^2*c - 5*a^5*b*c^2 + a^5*c^3 + 7*a^4*b^3*c - 2*a^4*b^2*c^2 + 7*a^4*b*c^3 + a^3*b^5 + 7*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 + 7*a^3*b*c^4 + a^3*c^5 + a^2*b^6 - 5*a^2*b^5*c - 2*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 2*a^2*b^2*c^4 - 5*a^2*b*c^5 + a^2*c^6 + 2*a*b^6*c - 5*a*b^5*c^2 + 7*a*b^4*c^3 + 7*a*b^3*c^4 - 5*a*b^2*c^5 + 2*a*b*c^6 + b^6*c^2 + b^5*c^3 + b^3*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*b^2 + 2*a^6*b*c + a^6*c^2 + a^5*b^3 - 5*a^5*b^2*c - 5*a^5*b*c^2 + a^5*c^3 + 7*a^4*b^3*c - 2*a^4*b^2*c^2 + 7*a^4*b*c^3 + a^3*b^5 + 7*a^3*b^4*c - 8*a^3*b^3*c^2 - 8*a^3*b^2*c^3 + 7*a^3*b*c^4 + a^3*c^5 + a^2*b^6 - 5*a^2*b^5*c - 2*a^2*b^4*c^2 - 8*a^2*b^3*c^3 - 2*a^2*b^2*c^4 - 5*a^2*b*c^5 + a^2*c^6 + 2*a*b^6*c - 5*a*b^5*c^2 + 7*a*b^4*c^3 + 7*a*b^3*c^4 - 5*a*b^2*c^5 + 2*a*b*c^6 + b^6*c^2 + b^5*c^3 + b^3*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a / (b + c) + b / (c + a)) * (b / (c + a) + c / (a + b)) * (c / (a + b) + a / (b + c)) ≥ 7 / 8 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + 1 / 8) := @solution
#print axioms solution
