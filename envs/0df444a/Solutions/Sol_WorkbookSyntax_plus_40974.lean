-- Prove2me | solution 1 for WorkbookSyntax.plus_40974
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:35.552617+00:00
-- url     : https://prove2.me/submissions/f64b6625-7624-4b26-921b-ef18ee880c97

/- InternLM Lean-Workbook, Apache-2.0. The obsolete finite-sum binder syntax is explicitly modernized. -/
import Mathlib
open Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
theorem solution : ∑ i ∈ Finset.Icc (1 : ℕ) 64, (1 : ℝ) / i < 6.4   := by
  norm_num [Finset.sum_Icc_succ_top]
example : (∑ i ∈ Finset.Icc (1 : ℕ) 64, (1 : ℝ) / i < 6.4) := @solution
#print axioms solution
