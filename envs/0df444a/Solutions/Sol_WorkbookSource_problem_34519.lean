-- Prove2me | solution 1 for WorkbookSource.problem_34519
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:39.726704+00:00
-- url     : https://prove2.me/submissions/1df9a98a-707e-4f6c-8359-01d921329c0e

/- Source: InternLM Lean-Workbook lean_workbook_34519, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution {a h k : ℕ} (h1 : Nat.Coprime h k) :  Nat.Coprime a h ∧ Nat.Coprime a k ↔ Nat.Coprime a (h * k) := by
  exact Nat.coprime_mul_iff_right.symm

example : (∀ {a h k : ℕ} (h1 : Nat.Coprime h k), Nat.Coprime a h ∧ Nat.Coprime a k ↔ Nat.Coprime a (h * k)) := @solution
#print axioms solution
