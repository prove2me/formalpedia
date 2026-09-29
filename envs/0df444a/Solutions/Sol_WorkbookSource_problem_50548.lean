-- Prove2me | solution 1 for WorkbookSource.problem_50548
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:25.607287+00:00
-- url     : https://prove2.me/submissions/a976f536-5047-4aea-b82c-8b45c9a377cf

/- Source: InternLM Lean-Workbook lean_workbook_50548, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (N₁ N₂ : ℤ) (h₁ : N₁ = -6) (h₂ : N₂ = 41) : N₁ * N₂ = -246 := by
  norm_num [h₁, h₂]

example : (∀ (N₁ N₂ : ℤ) (h₁ : N₁ = -6) (h₂ : N₂ = 41), N₁ * N₂ = -246) := @solution
#print axioms solution
