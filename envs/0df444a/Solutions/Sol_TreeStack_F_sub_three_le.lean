-- Prove2me | solution 1 for TreeStack.F_sub_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:47.132423+00:00
-- url     : https://prove2.me/submissions/d8ffdc67-e1b9-49b3-93a2-355730a3b530

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution (z : ℤ) : F (z - 3) ≤ F z := by
  unfold F
  split_ifs <;> omega
end TreeStack
