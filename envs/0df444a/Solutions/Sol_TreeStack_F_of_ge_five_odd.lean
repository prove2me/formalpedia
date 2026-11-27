-- Prove2me | solution 1 for TreeStack.F_of_ge_five_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:36.73084+00:00
-- url     : https://prove2.me/submissions/1fbf0bc4-c435-4e6f-a8f6-35a30287623e

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
import Theorems.Thm_TreeStack_empty_ne_integer_zero
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
theorem _root_.solution {x : ℤ} (h5 : 5 ≤ x) (ho : x % 2 ≠ 0) :
    F x = (x - 3) / 2 := by
  simp [F, show ¬ x ≤ 1 by omega, show x ≠ 2 by omega,
    show x ≠ 3 by omega, ho]
end TreeStack
