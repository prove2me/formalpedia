-- Prove2me | solution 1 for WorkbookSource.problem_40872
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:51.793908+00:00
-- url     : https://prove2.me/submissions/76b6914a-a64d-4edc-89b3-b9215d5d0543

/- InternLM Lean-Workbook, lean_workbook_40872, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y * z) * (y + z) ≥ 4 * x * y * z  := by
  first
  | solve
    | nlinarith [mul_nonneg (le_of_lt hy) (sq_nonneg (x-z)),mul_nonneg (le_of_lt hz) (sq_nonneg (x-y))]
  | solve
    | have : 0 ≤ (x - y)^2 + (x - z)^2 := by positivity
      nlinarith [hx, hy, hz]
  | solve
    | ring_nf
      have h1 : 0 ≤ (x - y)^2 + (x - z)^2 := by positivity
      nlinarith
  | solve
    | have h1 : 0 ≤ (x - y)^2 + (x - z)^2 := by nlinarith
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z)]
  | solve
    | have h2 : 0 ≤ (x - y)^2 + (x - z)^2 := by nlinarith
      nlinarith
  | solve
    | nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  | solve
    | ring_nf
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z)]
  | solve
    | have h1 : 0 ≤ (x - y)^2 := sq_nonneg (x - y)
      have h2 : 0 ≤ (x - z)^2 := sq_nonneg (x - z)
      nlinarith
  | solve
    | nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  | solve
    | ring_nf
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  | solve
    | have h3 : 0 ≤ (x - y)^2 + (x - z)^2 := by positivity
      nlinarith [h3]
  | solve
    | have := sq_nonneg (x - y)
      have := sq_nonneg (x - z)
      nlinarith
example : (∀ {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^2 + y * z) * (y + z) ≥ 4 * x * y * z) := @solution
#print axioms solution
