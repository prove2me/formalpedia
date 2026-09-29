-- Prove2me | solution 1 for WorkbookSyntax.plus_44878
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:06:30.650221+00:00
-- url     : https://prove2.me/submissions/8c46612c-877f-4e20-ab5f-9278f70adb59

/- InternLM Lean-Workbook, Apache-2.0. The obsolete finite-sum binder syntax is explicitly modernized. -/
import Mathlib
open Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
theorem solution (h₁ : 0 < 22) (h₂ : 0 < 15) : ∑ k ∈ Finset.range 11, (Nat.choose 22 (10 - k) * Nat.choose 15 k) = 348330136   := by
  decide +kernel
example : (∀ (h₁ : 0 < 22) (h₂ : 0 < 15), ∑ k ∈ Finset.range 11, (Nat.choose 22 (10 - k) * Nat.choose 15 k) = 348330136) := @solution
#print axioms solution
