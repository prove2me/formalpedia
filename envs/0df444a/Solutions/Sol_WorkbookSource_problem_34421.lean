-- Prove2me | solution 1 for WorkbookSource.problem_34421
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:38.919305+00:00
-- url     : https://prove2.me/submissions/13484f8b-c364-48b1-bc84-cd8d0195ddad

/- Source: InternLM Lean-Workbook lean_workbook_34421, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (j : ℕ) : (2 * j + 1 ≡ 4 [ZMOD 5]) ↔ j ≡ 4 [ZMOD 5] := by
  simp only [Int.ModEq]
  omega

example : (∀ (j : ℕ), (2 * j + 1 ≡ 4 [ZMOD 5]) ↔ j ≡ 4 [ZMOD 5]) := @solution
#print axioms solution
