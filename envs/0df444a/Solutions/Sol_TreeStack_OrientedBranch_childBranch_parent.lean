-- Prove2me | solution 1 for TreeStack.OrientedBranch.childBranch_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:04.928839+00:00
-- url     : https://prove2.me/submissions/e377f939-9e3e-488c-9bfc-f960cdb11aa3

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) (c : B.Child) :
    (B.childBranch c).parent = B.root := rfl
end TreeStack.OrientedBranch
