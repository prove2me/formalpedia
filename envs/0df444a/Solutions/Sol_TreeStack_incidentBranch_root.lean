-- Prove2me | solution 1 for TreeStack.incidentBranch_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:30:41.162796+00:00
-- url     : https://prove2.me/submissions/4373d719-cdd3-4d02-9af7-185b8bf5bf4b

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution (r u : V) (h : T.graph.Adj u r) :
    (incidentBranch T r u h).root = u := rfl
end TreeStack
