-- Prove2me | solution 1 for TreeStack.one_vertex_flux_attained_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:11.945934+00:00
-- url     : https://prove2.me/submissions/08d474ae-5631-4d4e-903a-0da5d767d648

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_of_ge_four_even
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.F_three

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {k : ℤ} (hk : 1 ≤ k) :
    let y : ℤ := 2 * k
    let A : ℤ := k
    let B : ℤ := 0
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  have hy : 4 ≤ 2 * k ∨ k = 1 := by omega
  rcases hy with hy | rfl
  · rw [F_of_ge_four_even hy (by omega)]
    omega
  · norm_num
end TreeStack
