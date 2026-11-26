-- Prove2me | solution 1 for TreeStack.OrientedBranch.root_ne_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:35.628525+00:00
-- url     : https://prove2.me/submissions/6f9bf295-2495-4af8-8cb8-9107e35a0b93

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) :
    B.root ≠ B.parent :=
  B.adj.ne
end TreeStack.OrientedBranch
