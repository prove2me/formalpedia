-- Prove2me | solution 1 for TreeStack.rootTasks_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:29.912843+00:00
-- url     : https://prove2.me/submissions/bf430735-8225-4a9e-86d2-b12c93d36127

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    (rootTasks T C r).Nodup := by
  classical
  exact Finset.nodup_toList (Finset.univ : Finset (RootTask T C r))
end TreeStack
