-- Prove2me | solution 1 for TreeStack.OrientedBranch.edgeBranch_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:54.438565+00:00
-- url     : https://prove2.me/submissions/57c96114-411a-4945-89b2-c144c7e0e2b4

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution (e : T.graph.edgeFinset) :
    s((edgeBranch (T := T) e).root, (edgeBranch (T := T) e).parent) = e.1 := by
  exact edgeDart_edge (T := T) e
end TreeStack.OrientedBranch
