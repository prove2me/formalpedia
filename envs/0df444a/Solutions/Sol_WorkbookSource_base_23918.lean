-- Prove2me | solution 1 for WorkbookSource.base_23918
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:11.047353+00:00
-- url     : https://prove2.me/submissions/c29f639f-4932-42c0-b1af-785f23776ce1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2) : (1 / (a ^ 3 + a) + 1 / (b ^ 3 + b) + 1 / (c ^ 3 + c)) ≤ 1 / (a * b * c)  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6/64 + a^5*b/32 + a^5*c/32 + 11*a^4*b^2/64 - 11*a^4*b*c/32 + 11*a^4*c^2/64 - 9*a^3*b^3/16 + 5*a^3*b^2*c/16 + 5*a^3*b*c^2/16 - 9*a^3*c^3/16 + 11*a^2*b^4/64 + 5*a^2*b^3*c/16 + 65*a^2*b^2*c^2/32 + 5*a^2*b*c^3/16 + 11*a^2*c^4/64 + a*b^5/32 - 11*a*b^4*c/32 + 5*a*b^3*c^2/16 + 5*a*b^2*c^3/16 - 11*a*b*c^4/32 + a*c^5/32 + 5*b^6/64 + b^5*c/32 + 11*b^4*c^2/64 - 9*b^3*c^3/16 + 11*b^2*c^4/64 + b*c^5/32 + 5*c^6/64) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (169/64 : ℝ) * a^6 + (169/16 : ℝ) * a^5 * (b - a)^1 + (169/32 : ℝ) * a^5 * (c - b)^1 + (33/2 : ℝ) * a^4 * (b - a)^2 + (33/2 : ℝ) * a^4 * (b - a)^1 * (c - b)^1 + (211/64 : ℝ) * a^4 * (c - b)^2 + (23/2 : ℝ) * a^3 * (b - a)^3 + (69/4 : ℝ) * a^3 * (b - a)^2 * (c - b)^1 + (73/8 : ℝ) * a^3 * (b - a)^1 * (c - b)^2 + (27/16 : ℝ) * a^3 * (c - b)^3 + (3 : ℝ) * a^2 * (b - a)^4 + (6 : ℝ) * a^2 * (b - a)^3 * (c - b)^1 + (17/2 : ℝ) * a^2 * (b - a)^2 * (c - b)^2 + (11/2 : ℝ) * a^2 * (b - a)^1 * (c - b)^3 + (95/64 : ℝ) * a^2 * (c - b)^4 + (7/2 : ℝ) * a^1 * (b - a)^3 * (c - b)^2 + (21/4 : ℝ) * a^1 * (b - a)^2 * (c - b)^3 + (45/16 : ℝ) * a^1 * (b - a)^1 * (c - b)^4 + (17/32 : ℝ) * a^1 * (c - b)^5 + (1 : ℝ) * (b - a)^4 * (c - b)^2 + (2 : ℝ) * (b - a)^3 * (c - b)^3 + (3/2 : ℝ) * (b - a)^2 * (c - b)^4 + (1/2 : ℝ) * (b - a)^1 * (c - b)^5 + (5/64 : ℝ) * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6/64 + a^5*b/32 + a^5*c/32 + 11*a^4*b^2/64 - 11*a^4*b*c/32 + 11*a^4*c^2/64 - 9*a^3*b^3/16 + 5*a^3*b^2*c/16 + 5*a^3*b*c^2/16 - 9*a^3*c^3/16 + 11*a^2*b^4/64 + 5*a^2*b^3*c/16 + 65*a^2*b^2*c^2/32 + 5*a^2*b*c^3/16 + 11*a^2*c^4/64 + a*b^5/32 - 11*a*b^4*c/32 + 5*a*b^3*c^2/16 + 5*a*b^2*c^3/16 - 11*a*b*c^4/32 + a*c^5/32 + 5*b^6/64 + b^5*c/32 + 11*b^4*c^2/64 - 9*b^3*c^3/16 + 11*b^2*c^4/64 + b*c^5/32 + 5*c^6/64) := by
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
  have he : (-a^3*b^3 - a^3*b - a^3*c^3 - a^3*c + a^2*b^2*c^2 + a^2*b^2 + a^2*c^2 + a^2 - a*b^3 - a*b - a*c^3 - a*c - b^3*c^3 - b^3*c + b^2*c^2 + b^2 - b*c^3 - b*c + c^2 + 1) = (5*a^6/64 + a^5*b/32 + a^5*c/32 + 11*a^4*b^2/64 - 11*a^4*b*c/32 + 11*a^4*c^2/64 - 9*a^3*b^3/16 + 5*a^3*b^2*c/16 + 5*a^3*b*c^2/16 - 9*a^3*c^3/16 + 11*a^2*b^4/64 + 5*a^2*b^3*c/16 + 65*a^2*b^2*c^2/32 + 5*a^2*b*c^3/16 + 11*a^2*c^4/64 + a*b^5/32 - 11*a*b^4*c/32 + 5*a*b^3*c^2/16 + 5*a*b^2*c^3/16 - 11*a*b*c^4/32 + a*c^5/32 + 5*b^6/64 + b^5*c/32 + 11*b^4*c^2/64 - 9*b^3*c^3/16 + 11*b^2*c^4/64 + b*c^5/32 + 5*c^6/64) := by
    linear_combination (-5*a^5/64 + 3*a^4*b/64 + 3*a^4*c/64 - 5*a^4/32 - 7*a^3*b^2/32 + a^3*b*c/4 + a^3*b/4 - 7*a^3*c^2/32 + a^3*c/4 - 5*a^3/16 - 7*a^2*b^3/32 - 11*a^2*b^2*c/32 - 11*a^2*b^2/16 - 11*a^2*b*c^2/32 - 3*a^2*b/16 - 7*a^2*c^3/32 - 11*a^2*c^2/16 - 3*a^2*c/16 - 5*a^2/8 + 3*a*b^4/64 + a*b^3*c/4 + a*b^3/4 - 11*a*b^2*c^2/32 - 3*a*b^2/16 + a*b*c^3/4 + 3*a*b*c/8 + a*b/4 + 3*a*c^4/64 + a*c^3/4 - 3*a*c^2/16 + a*c/4 - a/4 - 5*b^5/64 + 3*b^4*c/64 - 5*b^4/32 - 7*b^3*c^2/32 + b^3*c/4 - 5*b^3/16 - 7*b^2*c^3/32 - 11*b^2*c^2/16 - 3*b^2*c/16 - 5*b^2/8 + 3*b*c^4/64 + b*c^3/4 - 3*b*c^2/16 + b*c/4 - b/4 - 5*c^5/64 - 5*c^4/32 - 5*c^3/16 - 5*c^2/8 - c/4 - 1/2) * hab
  have hn : 0 ≤ (-a^3*b^3 - a^3*b - a^3*c^3 - a^3*c + a^2*b^2*c^2 + a^2*b^2 + a^2*c^2 + a^2 - a*b^3 - a*b - a*c^3 - a*c - b^3*c^3 - b^3*c + b^2*c^2 + b^2 - b*c^3 - b*c + c^2 + 1) := by nlinarith only [hp, he]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2), (1 / (a ^ 3 + a) + 1 / (b ^ 3 + b) + 1 / (c ^ 3 + c)) ≤ 1 / (a * b * c)) := @solution
#print axioms solution
