-- Prove2me | solution 1 for WorkbookSource.plus_32213
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:49:20.231701+00:00
-- url     : https://prove2.me/submissions/d9efdde7-6068-401c-b224-8040031ec27e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2) : (1 - b * c) * (1 - c * a) * (1 - a * b) ≥ (125 * a ^ 2 * b ^ 2 * c ^ 2) / 64   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - a^4*b^2 + 10*a^4*b*c - a^4*c^2 - 4*a^3*b^3 + 20*a^3*b^2*c + 20*a^3*b*c^2 - 4*a^3*c^3 - a^2*b^4 + 20*a^2*b^3*c - 147*a^2*b^2*c^2 + 20*a^2*b*c^3 - a^2*c^4 + 2*a*b^5 + 10*a*b^4*c + 20*a*b^3*c^2 + 20*a*b^2*c^3 + 10*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c - b^4*c^2 - 4*b^3*c^3 - b^2*c^4 + 2*b*c^5 + c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (90 : ℝ) * a^4 * (b - a)^2 + (90 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (90 : ℝ) * a^4 * (c - b)^2 + (236 : ℝ) * a^3 * (b - a)^3 + (354 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (366 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (124 : ℝ) * a^3 * (c - b)^3 + (211 : ℝ) * a^2 * (b - a)^4 + (422 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (483 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (272 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (43 : ℝ) * a^2 * (c - b)^4 + (64 : ℝ) * a^1 * (b - a)^5 + (160 : ℝ) * a^1 * (b - a)^4 * (c - b)^1 + (224 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (176 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (68 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (10 : ℝ) * a^1 * (c - b)^5 + (16 : ℝ) * (b - a)^4 * (c - b)^2 + (32 : ℝ) * (b - a)^3 * (c - b)^3 + (24 : ℝ) * (b - a)^2 * (c - b)^4 + (8 : ℝ) * (b - a)^1 * (c - b)^5 + (1 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (a^6 + 2*a^5*b + 2*a^5*c - a^4*b^2 + 10*a^4*b*c - a^4*c^2 - 4*a^3*b^3 + 20*a^3*b^2*c + 20*a^3*b*c^2 - 4*a^3*c^3 - a^2*b^4 + 20*a^2*b^3*c - 147*a^2*b^2*c^2 + 20*a^2*b*c^3 - a^2*c^4 + 2*a*b^5 + 10*a*b^4*c + 20*a*b^3*c^2 + 20*a*b^2*c^3 + 10*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c - b^4*c^2 - 4*b^3*c^3 - b^2*c^4 + 2*b*c^5 + c^6) := by
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
  have he : (-189*a^2*b^2*c^2 + 64*a^2*b*c + 64*a*b^2*c + 64*a*b*c^2 - 64*a*b - 64*a*c - 64*b*c + 64) = (a^6 + 2*a^5*b + 2*a^5*c - a^4*b^2 + 10*a^4*b*c - a^4*c^2 - 4*a^3*b^3 + 20*a^3*b^2*c + 20*a^3*b*c^2 - 4*a^3*c^3 - a^2*b^4 + 20*a^2*b^3*c - 147*a^2*b^2*c^2 + 20*a^2*b*c^3 - a^2*c^4 + 2*a*b^5 + 10*a*b^4*c + 20*a*b^3*c^2 + 20*a*b^2*c^3 + 10*a*b*c^4 + 2*a*c^5 + b^6 + 2*b^5*c - b^4*c^2 - 4*b^3*c^3 - b^2*c^4 + 2*b*c^5 + c^6) := by
    linear_combination (-a^5 - a^4*b - a^4*c - 2*a^4 + 2*a^3*b^2 - 8*a^3*b*c + 2*a^3*c^2 - 4*a^3 + 2*a^2*b^3 - 14*a^2*b^2*c + 4*a^2*b^2 - 14*a^2*b*c^2 - 16*a^2*b*c + 4*a^2*b + 2*a^2*c^3 + 4*a^2*c^2 + 4*a^2*c - 8*a^2 - a*b^4 - 8*a*b^3*c - 14*a*b^2*c^2 - 16*a*b^2*c + 4*a*b^2 - 8*a*b*c^3 - 16*a*b*c^2 + 24*a*b*c + 16*a*b - a*c^4 + 4*a*c^2 + 16*a*c - 16*a - b^5 - b^4*c - 2*b^4 + 2*b^3*c^2 - 4*b^3 + 2*b^2*c^3 + 4*b^2*c^2 + 4*b^2*c - 8*b^2 - b*c^4 + 4*b*c^2 + 16*b*c - 16*b - c^5 - 2*c^4 - 4*c^3 - 8*c^2 - 16*c - 32) * hab
  have hn : 0 ≤ (-189*a^2*b^2*c^2 + 64*a^2*b*c + 64*a*b^2*c + 64*a*b*c^2 - 64*a*b - 64*a*c - 64*b*c + 64) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2), (1 - b * c) * (1 - c * a) * (1 - a * b) ≥ (125 * a ^ 2 * b ^ 2 * c ^ 2) / 64) := @solution
#print axioms solution
