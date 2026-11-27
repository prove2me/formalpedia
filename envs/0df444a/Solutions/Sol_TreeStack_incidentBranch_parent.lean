-- Prove2me | solution 1 for TreeStack.incidentBranch_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:30:41.608797+00:00
-- url     : https://prove2.me/submissions/1dedd8ea-2864-4d0c-af30-8ef38bc98e27

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution (r u : V) (h : T.graph.Adj u r) :
    (incidentBranch T r u h).parent = r := rfl
end TreeStack
