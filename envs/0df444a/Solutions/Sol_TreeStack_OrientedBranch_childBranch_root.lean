-- Prove2me | solution 1 for TreeStack.OrientedBranch.childBranch_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:51.470035+00:00
-- url     : https://prove2.me/submissions/e28b7b86-4c4b-4125-8852-fc84bcf8f66d

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).root = c.vertex := rfl
end TreeStack.OrientedBranch
