-- Prove2me | solution 1 for TreeStack.one_vertex_flux_attained_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:14.841868+00:00
-- url     : https://prove2.me/submissions/34e26f49-8ea2-48d6-85e3-65570e2349cf

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_of_ge_five_odd
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.F_three

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {k : ℤ} (hk : 1 ≤ k) :
    let y : ℤ := 2 * k + 1
    let A : ℤ := k + 1
    let B : ℤ := 1
    1 ≤ A ∧ 0 ≤ B ∧ y + B - 2 * A = 0 ∧ A - 2 * B = F y := by
  dsimp
  by_cases hk1 : k = 1
  · subst k
    norm_num
  · have hy : 5 ≤ 2 * k + 1 := by omega
    rw [F_of_ge_five_odd hy (by omega)]
    omega
end TreeStack
