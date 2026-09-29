-- Prove2me | solution 1 for WorkbookSource.plus_353
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:44:05.057268+00:00
-- url     : https://prove2.me/submissions/15f2d9bb-669a-4e65-9cc2-4d0686de426b

/- Source: InternLM Lean-Workbook lean_workbook_plus_353, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000
theorem solution (X Y : Prop) : X → Y ↔ ¬(X ∧ ¬Y) := by
  tauto

example : (∀ (X Y : Prop), X → Y ↔ ¬(X ∧ ¬Y)) := @solution
#print axioms solution

example (X Y : Prop) : ((X → Y) ↔ ¬(X ∧ ¬Y)) := solution X Y
