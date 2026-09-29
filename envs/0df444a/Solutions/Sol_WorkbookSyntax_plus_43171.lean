-- Prove2me | solution 1 for WorkbookSyntax.plus_43171
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:37.231085+00:00
-- url     : https://prove2.me/submissions/df347406-cfcd-4219-9b6b-db26be460541

/- InternLM Lean-Workbook, Apache-2.0. The obsolete finite-sum binder syntax is explicitly modernized. -/
import Mathlib
open Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
theorem solution : ∑ k ∈ Finset.filter (λ x => 2∣x ∨ 3∣x ∨ 5∣x) (Finset.Icc 1 2004), 1 = 1469   := by
  decide +kernel
example : (∑ k ∈ Finset.filter (λ x => 2∣x ∨ 3∣x ∨ 5∣x) (Finset.Icc 1 2004), 1 = 1469) := @solution
#print axioms solution
