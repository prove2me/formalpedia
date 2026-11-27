-- Prove2me | solution 1 for TreeStack.RootTask.branch_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:30:51.485853+00:00
-- url     : https://prove2.me/submissions/6f109741-a678-4ab4-8521-0ebc97ca6a2d

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
    t.branch.parent = r := rfl
end RootTask
end TreeStack
