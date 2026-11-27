-- Prove2me | solution 1 for TreeStack.RootTask.branch_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:30:42.164149+00:00
-- url     : https://prove2.me/submissions/73d59cd9-0efb-41d9-9be4-f540ecea2b4b

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
    t.branch.root = t.1 := rfl
end RootTask
end TreeStack
