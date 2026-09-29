-- Prove2me | solution 1 for WorkbookSource.problem_44968
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:41.98396+00:00
-- url     : https://prove2.me/submissions/7d8bdf22-37c8-4c1d-932d-2dc098e20428

/- Source: InternLM Lean-Workbook lean_workbook_44968, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (n : ℕ) (hn : n = 83) : φ n = 82 := by
  subst n
  exact Nat.totient_prime (by norm_num : Nat.Prime 83)

example : (∀ (n : ℕ) (hn : n = 83), φ n = 82) := @solution
#print axioms solution
