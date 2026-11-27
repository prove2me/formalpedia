-- Prove2me | solution 1 for TreeStack.F_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:02.93695+00:00
-- url     : https://prove2.me/submissions/eb41deda-de0d-4e31-8af1-4c76d77e1c95

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution (z : ℤ) : F z = 0 ↔ z = 3 := by
  unfold F
  split_ifs <;> omega
end TreeStack
