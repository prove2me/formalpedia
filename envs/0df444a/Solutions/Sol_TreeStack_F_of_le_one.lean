-- Prove2me | solution 1 for TreeStack.F_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:27.861096+00:00
-- url     : https://prove2.me/submissions/accd42f0-c674-454d-beaa-d8432e8cca00

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.empty_ne_integer_zero

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {x : ℤ} (h : x ≤ 1) : F x = 2 * x - 3 := by
  simp [F, h]
end TreeStack
