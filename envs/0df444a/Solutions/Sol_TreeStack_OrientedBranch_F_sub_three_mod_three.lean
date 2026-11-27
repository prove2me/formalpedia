-- Prove2me | solution 1 for TreeStack.OrientedBranch.F_sub_three_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:51.620776+00:00
-- url     : https://prove2.me/submissions/d0704ad0-cfca-4c49-b83b-65cb539bceb6

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution (z : ℤ) :
    F (z - 3) % 3 = F z % 3 := by
  unfold F
  split_ifs <;> omega
end TreeStack.OrientedBranch
