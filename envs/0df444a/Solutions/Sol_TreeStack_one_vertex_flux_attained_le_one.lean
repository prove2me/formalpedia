-- Prove2me | solution 1 for TreeStack.one_vertex_flux_attained_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:01.93602+00:00
-- url     : https://prove2.me/submissions/50d17460-16f6-4e70-a5e8-6b7df4633aed

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_F_of_le_one
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.F_three

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {y : ℤ} (hy : y ≤ 1) :
    let A : ℤ := 1
    let B : ℤ := 2 - y
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  rw [F_of_le_one hy]
  omega
end TreeStack
