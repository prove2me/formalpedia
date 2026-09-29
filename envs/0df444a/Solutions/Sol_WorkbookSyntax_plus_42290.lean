-- Prove2me | solution 1 for WorkbookSyntax.plus_42290
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:29.830887+00:00
-- url     : https://prove2.me/submissions/c3812b83-a44f-4ec7-beb9-dcfb34d59a9e

/- InternLM Lean-Workbook, Apache-2.0. The obsolete finite-sum binder syntax is explicitly modernized. -/
import Mathlib
open Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
theorem solution :
  ∑ k ∈ (Finset.range 20), (2^k) % 25 = 250   := by
  decide +kernel
example : (∑ k ∈ (Finset.range 20), (2^k) % 25 = 250) := @solution
#print axioms solution
