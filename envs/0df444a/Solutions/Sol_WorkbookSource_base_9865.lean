-- Prove2me | solution 1 for WorkbookSource.base_9865
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T01:46:42.85221+00:00
-- url     : https://prove2.me/submissions/e2f8c2db-9bb6-427b-8a25-e6797034e9fc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (c + a) / b + (a + b) / c ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b)) + (2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c)) / (a + b + c) ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6*b^2 - 2*a^6*b*c + a^6*c^2 + 4*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 4*a^5*c^3 + 6*a^4*b^4 + 4*a^4*b^3*c - 8*a^4*b^2*c^2 + 4*a^4*b*c^3 + 6*a^4*c^4 + 4*a^3*b^5 + 4*a^3*b^4*c - 6*a^3*b^3*c^2 - 6*a^3*b^2*c^3 + 4*a^3*b*c^4 + 4*a^3*c^5 + a^2*b^6 - 4*a^2*b^5*c - 8*a^2*b^4*c^2 - 6*a^2*b^3*c^3 - 8*a^2*b^2*c^4 - 4*a^2*b*c^5 + a^2*c^6 - 2*a*b^6*c - 4*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 4*a*b^2*c^5 - 2*a*b*c^6 + b^6*c^2 + 4*b^5*c^3 + 6*b^4*c^4 + 4*b^3*c^5 + b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (56 : ℝ) * a^6 * (b - a)^2 + (56 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (56 : ℝ) * a^6 * (c - b)^2 + (284 : ℝ) * a^5 * (b - a)^3 + (426 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (246 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (52 : ℝ) * a^5 * (c - b)^3 + (592 : ℝ) * a^4 * (b - a)^4 + (1184 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (746 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (154 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (12 : ℝ) * a^4 * (c - b)^4 + (648 : ℝ) * a^3 * (b - a)^5 + (1620 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (1344 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (396 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (24 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (392 : ℝ) * a^2 * (b - a)^6 + (1176 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1271 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (582 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (95 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (124 : ℝ) * a^1 * (b - a)^7 + (434 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (586 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (380 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (118 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (14 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (16 : ℝ) * (b - a)^8 + (64 : ℝ) * (b - a)^7 * (c - b)^1 + (104 : ℝ) * (b - a)^6 * (c - b)^2 + (88 : ℝ) * (b - a)^5 * (c - b)^3 + (41 : ℝ) * (b - a)^4 * (c - b)^4 + (10 : ℝ) * (b - a)^3 * (c - b)^5 + (1 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6*b^2 - 2*a^6*b*c + a^6*c^2 + 4*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 4*a^5*c^3 + 6*a^4*b^4 + 4*a^4*b^3*c - 8*a^4*b^2*c^2 + 4*a^4*b*c^3 + 6*a^4*c^4 + 4*a^3*b^5 + 4*a^3*b^4*c - 6*a^3*b^3*c^2 - 6*a^3*b^2*c^3 + 4*a^3*b*c^4 + 4*a^3*c^5 + a^2*b^6 - 4*a^2*b^5*c - 8*a^2*b^4*c^2 - 6*a^2*b^3*c^3 - 8*a^2*b^2*c^4 - 4*a^2*b*c^5 + a^2*c^6 - 2*a*b^6*c - 4*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 4*a*b^2*c^5 - 2*a*b*c^6 + b^6*c^2 + 4*b^5*c^3 + 6*b^4*c^4 + 4*b^3*c^5 + b^2*c^6) := by
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
  have hn : 0 ≤ (a^6*b^2 - 2*a^6*b*c + a^6*c^2 + 4*a^5*b^3 - 4*a^5*b^2*c - 4*a^5*b*c^2 + 4*a^5*c^3 + 6*a^4*b^4 + 4*a^4*b^3*c - 8*a^4*b^2*c^2 + 4*a^4*b*c^3 + 6*a^4*c^4 + 4*a^3*b^5 + 4*a^3*b^4*c - 6*a^3*b^3*c^2 - 6*a^3*b^2*c^3 + 4*a^3*b*c^4 + 4*a^3*c^5 + a^2*b^6 - 4*a^2*b^5*c - 8*a^2*b^4*c^2 - 6*a^2*b^3*c^3 - 8*a^2*b^2*c^4 - 4*a^2*b*c^5 + a^2*c^6 - 2*a*b^6*c - 4*a*b^5*c^2 + 4*a*b^4*c^3 + 4*a*b^3*c^4 - 4*a*b^2*c^5 - 2*a*b*c^6 + b^6*c^2 + 4*b^5*c^3 + 6*b^4*c^4 + 4*b^3*c^5 + b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (b + c) / a + (c + a) / b + (a + b) / c ≥ 4 * (a / (b + c) + b / (c + a) + c / (a + b)) + (2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c)) / (a + b + c) ^ 2) := @solution
#print axioms solution
