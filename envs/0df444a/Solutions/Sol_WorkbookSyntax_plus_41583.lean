-- Prove2me | solution 1 for WorkbookSyntax.plus_41583
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:36.366954+00:00
-- url     : https://prove2.me/submissions/16ea1e62-0ed5-4c51-9a48-55bae52c9289

/- InternLM Lean-Workbook, Apache-2.0. The obsolete finite-sum binder syntax is explicitly modernized. -/
import Mathlib
open Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
theorem solution : ∑ x ∈ Finset.Icc 1 3, 2 * x = 12   := by
  decide +kernel
example : (∑ x ∈ Finset.Icc 1 3, 2 * x = 12) := @solution
#print axioms solution
