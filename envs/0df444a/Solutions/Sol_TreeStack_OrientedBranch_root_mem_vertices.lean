-- Prove2me | solution 1 for TreeStack.OrientedBranch.root_mem_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:40.70681+00:00
-- url     : https://prove2.me/submissions/f3c0aa0e-4e0b-401f-a442-0b76c9ecf494

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Branch

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (B : OrientedBranch T) :
    B.root ∈ B.vertices := by
  classical
  rw [vertices, Set.mem_toFinset]
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
end TreeStack.OrientedBranch
