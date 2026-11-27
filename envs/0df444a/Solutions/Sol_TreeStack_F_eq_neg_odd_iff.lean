-- Prove2me | solution 1 for TreeStack.F_eq_neg_odd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:14.348874+00:00
-- url     : https://prove2.me/submissions/793a14a3-e6d6-4c8d-84ed-9c9a66d5d13f

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {z r : ℤ} (hr : 0 ≤ r) :
    F z = -(2 * r + 1) ↔ z = 1 - r := by
  unfold F
  split_ifs <;> omega
end TreeStack
