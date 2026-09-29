-- Prove2me | solution 1 for WorkbookSource.base_14272
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:21.61082+00:00
-- url     : https://prove2.me/submissions/afa324b4-402b-4b38-8358-f3234f00a983

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) : 28 * a ^ 6 + 44 * a ^ 5 * v + 20 * a ^ 4 * v ^ 2 - 10 * a ^ 3 * v ^ 3 - 2 * a ^ 2 * v ^ 4 + 7 * a * v ^ 5 + 4 * v ^ 6 ≥ 0  := by
  have hp : 0 ≤ (28*a^6 + 44*a^5*v + 20*a^4*v^2 - 10*a^3*v^3 - 2*a^2*v^4 + 7*a*v^5 + 4*v^6) := by
    rcases le_total a v with hab | hba
    ·
      have hdiff1 : 0 ≤ (v - a) := by linarith
      have hpos : 0 ≤ (91 : ℝ) * a^6 + (105 : ℝ) * a^5 * (v - a)^1 + (108 : ℝ) * a^4 * (v - a)^2 + (132 : ℝ) * a^3 * (v - a)^3 + (93 : ℝ) * a^2 * (v - a)^4 + (31 : ℝ) * a^1 * (v - a)^5 + (4 : ℝ) * (v - a)^6 := by positivity
      convert hpos using 1 <;> ring
    ·
      have hdiff1 : 0 ≤ (a - v) := by linarith
      have hpos : 0 ≤ (91 : ℝ) * v^6 + (441 : ℝ) * v^5 * (a - v)^1 + (948 : ℝ) * v^4 * (a - v)^2 + (1070 : ℝ) * v^3 * (a - v)^3 + (660 : ℝ) * v^2 * (a - v)^4 + (212 : ℝ) * v^1 * (a - v)^5 + (28 : ℝ) * (a - v)^6 := by positivity
      convert hpos using 1 <;> ring
  nlinarith only [hp]
example : (∀ (a v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v), 28 * a ^ 6 + 44 * a ^ 5 * v + 20 * a ^ 4 * v ^ 2 - 10 * a ^ 3 * v ^ 3 - 2 * a ^ 2 * v ^ 4 + 7 * a * v ^ 5 + 4 * v ^ 6 ≥ 0) := @solution
#print axioms solution
