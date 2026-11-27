-- Prove2me | solution 1 for TreeStack.RootTask.occupied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:31:10.546604+00:00
-- url     : https://prove2.me/submissions/05aa5a05-884f-4c22-8d7a-18ffdd792e5d

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
namespace RootTask
theorem _root_.solution
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) :
    t.branch.Occupied C := by
  exact Classical.choose_spec t.2
end RootTask
end TreeStack
