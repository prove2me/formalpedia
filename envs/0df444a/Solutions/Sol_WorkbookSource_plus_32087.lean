-- Prove2me | solution 1 for WorkbookSource.plus_32087
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:44:35.139364+00:00
-- url     : https://prove2.me/submissions/cdd3fed2-ca6e-4185-9433-a25f0d619d53

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≥ 7 / (a ^ 2 + b ^ 2 + c ^ 2) + 2 / (a * b + b * c + a * c)   := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (6*a^6*b^2 + 8*a^6*b*c + 6*a^6*c^2 + 4*a^5*b^3 + 7*a^5*b^2*c + 7*a^5*b*c^2 + 4*a^5*c^3 - 16*a^4*b^4 + a^4*b^3*c - 11*a^4*b^2*c^2 + a^4*b*c^3 - 16*a^4*c^4 + 4*a^3*b^5 + a^3*b^4*c - 17*a^3*b^3*c^2 - 17*a^3*b^2*c^3 + a^3*b*c^4 + 4*a^3*c^5 + 6*a^2*b^6 + 7*a^2*b^5*c - 11*a^2*b^4*c^2 - 17*a^2*b^3*c^3 - 11*a^2*b^2*c^4 + 7*a^2*b*c^5 + 6*a^2*c^6 + 8*a*b^6*c + 7*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 7*a*b^2*c^5 + 8*a*b*c^6 + 6*b^6*c^2 + 4*b^5*c^3 - 16*b^4*c^4 + 4*b^3*c^5 + 6*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (189 : ℝ) * a^6 * (b - a)^2 + (189 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (189 : ℝ) * a^6 * (c - b)^2 + (702 : ℝ) * a^5 * (b - a)^3 + (1053 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (1215 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (432 : ℝ) * a^5 * (c - b)^3 + (1044 : ℝ) * a^4 * (b - a)^4 + (2088 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (2862 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (1818 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (369 : ℝ) * a^4 * (c - b)^4 + (794 : ℝ) * a^3 * (b - a)^5 + (1985 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (3206 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (2824 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1093 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (142 : ℝ) * a^3 * (c - b)^5 + (323 : ℝ) * a^2 * (b - a)^6 + (969 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (1842 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (2069 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1146 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (273 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (20 : ℝ) * a^2 * (c - b)^6 + (64 : ℝ) * a^1 * (b - a)^7 + (224 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (518 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (735 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (532 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (175 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (20 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (4 : ℝ) * (b - a)^8 + (16 : ℝ) * (b - a)^7 * (c - b)^1 + (52 : ℝ) * (b - a)^6 * (c - b)^2 + (100 : ℝ) * (b - a)^5 * (c - b)^3 + (94 : ℝ) * (b - a)^4 * (c - b)^4 + (40 : ℝ) * (b - a)^3 * (c - b)^5 + (6 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (6*a^6*b^2 + 8*a^6*b*c + 6*a^6*c^2 + 4*a^5*b^3 + 7*a^5*b^2*c + 7*a^5*b*c^2 + 4*a^5*c^3 - 16*a^4*b^4 + a^4*b^3*c - 11*a^4*b^2*c^2 + a^4*b*c^3 - 16*a^4*c^4 + 4*a^3*b^5 + a^3*b^4*c - 17*a^3*b^3*c^2 - 17*a^3*b^2*c^3 + a^3*b*c^4 + 4*a^3*c^5 + 6*a^2*b^6 + 7*a^2*b^5*c - 11*a^2*b^4*c^2 - 17*a^2*b^3*c^3 - 11*a^2*b^2*c^4 + 7*a^2*b*c^5 + 6*a^2*c^6 + 8*a*b^6*c + 7*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 7*a*b^2*c^5 + 8*a*b*c^6 + 6*b^6*c^2 + 4*b^5*c^3 - 16*b^4*c^4 + 4*b^3*c^5 + 6*b^2*c^6) := by
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
  have hn : 0 ≤ (6*a^6*b^2 + 8*a^6*b*c + 6*a^6*c^2 + 4*a^5*b^3 + 7*a^5*b^2*c + 7*a^5*b*c^2 + 4*a^5*c^3 - 16*a^4*b^4 + a^4*b^3*c - 11*a^4*b^2*c^2 + a^4*b*c^3 - 16*a^4*c^4 + 4*a^3*b^5 + a^3*b^4*c - 17*a^3*b^3*c^2 - 17*a^3*b^2*c^3 + a^3*b*c^4 + 4*a^3*c^5 + 6*a^2*b^6 + 7*a^2*b^5*c - 11*a^2*b^4*c^2 - 17*a^2*b^3*c^3 - 11*a^2*b^2*c^4 + 7*a^2*b*c^5 + 6*a^2*c^6 + 8*a*b^6*c + 7*a*b^5*c^2 + a*b^4*c^3 + a*b^3*c^4 + 7*a*b^2*c^5 + 8*a*b*c^6 + 6*b^6*c^2 + 4*b^5*c^3 - 16*b^4*c^4 + 4*b^3*c^5 + 6*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), 3 * (1 / (2 * a ^ 2 + b * c) + 1 / (2 * b ^ 2 + c * a) + 1 / (2 * c ^ 2 + a * b)) ≥ 7 / (a ^ 2 + b ^ 2 + c ^ 2) + 2 / (a * b + b * c + a * c)) := @solution
#print axioms solution
