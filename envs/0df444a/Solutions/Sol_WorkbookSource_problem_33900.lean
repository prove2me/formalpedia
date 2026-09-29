-- Prove2me | solution 1 for WorkbookSource.problem_33900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:37.81351+00:00
-- url     : https://prove2.me/submissions/99358d3c-8c8a-49c8-96d6-48d9296d240e

/- Source: InternLM Lean-Workbook lean_workbook_33900, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (b : ℕ → ℚ) (a : ℕ → ℚ) (b0 : b 0 = 3) (a0 : a 0 = 2) (hb : ∀ n, b (n + 1) = (b n)^2 / a n) (ha : ∀ n, a (n + 1) = (a n)^2 / b n) : b 8 = (3^3281)/2^3280 := by
  norm_num [hb, ha, b0, a0]

example : (∀ (b : ℕ → ℚ) (a : ℕ → ℚ) (b0 : b 0 = 3) (a0 : a 0 = 2) (hb : ∀ n, b (n + 1) = (b n)^2 / a n) (ha : ∀ n, a (n + 1) = (a n)^2 / b n), b 8 = (3^3281)/2^3280) := @solution
#print axioms solution
