-- Prove2me | solution 1 for WorkbookSource.plus_17740
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:28.800858+00:00
-- url     : https://prove2.me/submissions/930f35ee-7edd-4fd9-acf2-340f44453cea

/- Source: InternLM Lean-Workbook lean_workbook_plus_17740, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (P : ℕ → Prop) : (∀ N, ∃ n > N, P n) ↔ ¬ (∃ N, ∀ n > N, ¬ P n) := by
  simp only [not_exists, not_forall, not_not, exists_prop]

example : (∀ (P : ℕ → Prop), (∀ N, ∃ n > N, P n) ↔ ¬ (∃ N, ∀ n > N, ¬ P n)) := @solution
#print axioms solution
