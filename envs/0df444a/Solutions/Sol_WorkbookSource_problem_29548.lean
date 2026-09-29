-- Prove2me | solution 1 for WorkbookSource.problem_29548
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:40:35.131694+00:00
-- url     : https://prove2.me/submissions/149001d2-b516-423d-8ecf-688c86270483

/- Source: InternLM Lean-Workbook lean_workbook_29548, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
open scoped Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option exponentiation.threshold 5000
theorem solution (a : ℕ → ℤ) (a0 : a 0 = 2) (a1 : a 1 = 9) (a_rec : ∀ n, n ≥ 2 → a n = 2 * a (n - 1) - 4 * a (n - 2)) : a 15 = -2^16 := by
  have ha2 := a_rec 2 (by norm_num)
  norm_num [a1, a0] at ha2
  have ha3 := a_rec 3 (by norm_num)
  norm_num [ha2, a1] at ha3
  have ha4 := a_rec 4 (by norm_num)
  norm_num [ha3, ha2] at ha4
  have ha5 := a_rec 5 (by norm_num)
  norm_num [ha4, ha3] at ha5
  have ha6 := a_rec 6 (by norm_num)
  norm_num [ha5, ha4] at ha6
  have ha7 := a_rec 7 (by norm_num)
  norm_num [ha6, ha5] at ha7
  have ha8 := a_rec 8 (by norm_num)
  norm_num [ha7, ha6] at ha8
  have ha9 := a_rec 9 (by norm_num)
  norm_num [ha8, ha7] at ha9
  have ha10 := a_rec 10 (by norm_num)
  norm_num [ha9, ha8] at ha10
  have ha11 := a_rec 11 (by norm_num)
  norm_num [ha10, ha9] at ha11
  have ha12 := a_rec 12 (by norm_num)
  norm_num [ha11, ha10] at ha12
  have ha13 := a_rec 13 (by norm_num)
  norm_num [ha12, ha11] at ha13
  have ha14 := a_rec 14 (by norm_num)
  norm_num [ha13, ha12] at ha14
  have ha15 := a_rec 15 (by norm_num)
  norm_num [ha14, ha13] at ha15
  norm_num
  exact ha15

example : (∀ (a : ℕ → ℤ) (a0 : a 0 = 2) (a1 : a 1 = 9) (a_rec : ∀ n, n ≥ 2 → a n = 2 * a (n - 1) - 4 * a (n - 2)), a 15 = -2^16) := @solution
#print axioms solution
