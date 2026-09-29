-- Prove2me | solution 1 for WorkbookSource.base_24579
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T04:02:14.163796+00:00
-- url     : https://prove2.me/submissions/2eeb5608-ec05-4a42-80bf-ad59dddf85f0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a * b + b * c + c * a) ^ 2) ≥ 1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + a) ^ 2  := by
  have haux0 (a b c : ℝ) (hlow : 0 ≤ a) (hord1 : a ≤ b) (hord2 : b ≤ c) : 0 ≤ (5*a^6*b^2 + 10*a^6*b*c + 5*a^6*c^2 + 10*a^5*b^3 + 22*a^5*b^2*c + 22*a^5*b*c^2 + 10*a^5*c^3 + 6*a^4*b^4 - 16*a^4*b^2*c^2 + 6*a^4*c^4 + 10*a^3*b^5 - 74*a^3*b^3*c^2 - 74*a^3*b^2*c^3 + 10*a^3*c^5 + 5*a^2*b^6 + 22*a^2*b^5*c - 16*a^2*b^4*c^2 - 74*a^2*b^3*c^3 - 16*a^2*b^2*c^4 + 22*a^2*b*c^5 + 5*a^2*c^6 + 10*a*b^6*c + 22*a*b^5*c^2 + 22*a*b^2*c^5 + 10*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3 + 6*b^4*c^4 + 10*b^3*c^5 + 5*b^2*c^6) := by
    have hdiff1 : 0 ≤ (b - a) := by linarith
    have hdiff2 : 0 ≤ (c - b) := by linarith
    have hpos : 0 ≤ (480 : ℝ) * a^6 * (b - a)^2 + (480 : ℝ) * a^6 * (b - a)^1 * (c - b)^1 + (480 : ℝ) * a^6 * (c - b)^2 + (1984 : ℝ) * a^5 * (b - a)^3 + (2976 : ℝ) * a^5 * (b - a)^2 * (c - b)^1 + (2784 : ℝ) * a^5 * (b - a)^1 * (c - b)^2 + (896 : ℝ) * a^5 * (c - b)^3 + (3336 : ℝ) * a^4 * (b - a)^4 + (6672 : ℝ) * a^4 * (b - a)^3 * (c - b)^1 + (6808 : ℝ) * a^4 * (b - a)^2 * (c - b)^2 + (3472 : ℝ) * a^4 * (b - a)^1 * (c - b)^3 + (616 : ℝ) * a^4 * (c - b)^4 + (2920 : ℝ) * a^3 * (b - a)^5 + (7300 : ℝ) * a^3 * (b - a)^4 * (c - b)^1 + (8488 : ℝ) * a^3 * (b - a)^3 * (c - b)^2 + (5432 : ℝ) * a^3 * (b - a)^2 * (c - b)^3 + (1692 : ℝ) * a^3 * (b - a)^1 * (c - b)^4 + (184 : ℝ) * a^3 * (c - b)^5 + (1404 : ℝ) * a^2 * (b - a)^6 + (4212 : ℝ) * a^2 * (b - a)^5 * (c - b)^1 + (5611 : ℝ) * a^2 * (b - a)^4 * (c - b)^2 + (4202 : ℝ) * a^2 * (b - a)^3 * (c - b)^3 + (1735 : ℝ) * a^2 * (b - a)^2 * (c - b)^4 + (336 : ℝ) * a^2 * (b - a)^1 * (c - b)^5 + (20 : ℝ) * a^2 * (c - b)^6 + (352 : ℝ) * a^1 * (b - a)^7 + (1232 : ℝ) * a^1 * (b - a)^6 * (c - b)^1 + (1868 : ℝ) * a^1 * (b - a)^5 * (c - b)^2 + (1590 : ℝ) * a^1 * (b - a)^4 * (c - b)^3 + (784 : ℝ) * a^1 * (b - a)^3 * (c - b)^4 + (202 : ℝ) * a^1 * (b - a)^2 * (c - b)^5 + (20 : ℝ) * a^1 * (b - a)^1 * (c - b)^6 + (36 : ℝ) * (b - a)^8 + (144 : ℝ) * (b - a)^7 * (c - b)^1 + (246 : ℝ) * (b - a)^6 * (c - b)^2 + (234 : ℝ) * (b - a)^5 * (c - b)^3 + (131 : ℝ) * (b - a)^4 * (c - b)^4 + (40 : ℝ) * (b - a)^3 * (c - b)^5 + (5 : ℝ) * (b - a)^2 * (c - b)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (5*a^6*b^2 + 10*a^6*b*c + 5*a^6*c^2 + 10*a^5*b^3 + 22*a^5*b^2*c + 22*a^5*b*c^2 + 10*a^5*c^3 + 6*a^4*b^4 - 16*a^4*b^2*c^2 + 6*a^4*c^4 + 10*a^3*b^5 - 74*a^3*b^3*c^2 - 74*a^3*b^2*c^3 + 10*a^3*c^5 + 5*a^2*b^6 + 22*a^2*b^5*c - 16*a^2*b^4*c^2 - 74*a^2*b^3*c^3 - 16*a^2*b^2*c^4 + 22*a^2*b*c^5 + 5*a^2*c^6 + 10*a*b^6*c + 22*a*b^5*c^2 + 22*a*b^2*c^5 + 10*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3 + 6*b^4*c^4 + 10*b^3*c^5 + 5*b^2*c^6) := by
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
  have hn : 0 ≤ (5*a^6*b^2 + 10*a^6*b*c + 5*a^6*c^2 + 10*a^5*b^3 + 22*a^5*b^2*c + 22*a^5*b*c^2 + 10*a^5*c^3 + 6*a^4*b^4 - 16*a^4*b^2*c^2 + 6*a^4*c^4 + 10*a^3*b^5 - 74*a^3*b^3*c^2 - 74*a^3*b^2*c^3 + 10*a^3*c^5 + 5*a^2*b^6 + 22*a^2*b^5*c - 16*a^2*b^4*c^2 - 74*a^2*b^3*c^3 - 16*a^2*b^2*c^4 + 22*a^2*b*c^5 + 5*a^2*c^6 + 10*a*b^6*c + 22*a*b^5*c^2 + 22*a*b^2*c^5 + 10*a*b*c^6 + 5*b^6*c^2 + 10*b^5*c^3 + 6*b^4*c^4 + 10*b^3*c^5 + 5*b^2*c^6) := by nlinarith only [hp]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (9 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a * b + b * c + c * a) ^ 2) ≥ 1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + a) ^ 2) := @solution
#print axioms solution
