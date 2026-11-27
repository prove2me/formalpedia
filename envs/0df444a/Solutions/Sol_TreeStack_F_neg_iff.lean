-- Prove2me | solution 1 for TreeStack.F_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:56.976737+00:00
-- url     : https://prove2.me/submissions/72d7576a-31f1-43cd-8bbb-2e31db0b059b

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution (z : ℤ) : F z < 0 ↔ z ≤ 1 := by
  unfold F
  split_ifs <;> omega
end TreeStack
