-- Prove2me | solution 1 for TreeStack.mem_rootTasks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:31:27.317727+00:00
-- url     : https://prove2.me/submissions/54977bef-2f0c-4178-9964-376e63464795

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (t : RootTask T C r) :
    t ∈ rootTasks T C r := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ t)
end TreeStack
