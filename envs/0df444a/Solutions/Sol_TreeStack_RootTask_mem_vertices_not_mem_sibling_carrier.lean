-- Prove2me | solution 1 for TreeStack.RootTask.mem_vertices_not_mem_sibling_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:53:49.900408+00:00
-- url     : https://prove2.me/submissions/567dc22c-75f5-4ead-9520-3c08f6d70985

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_mem_incidentBranch_vertices_not_mem_sibling_carrier

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
namespace RootTask
theorem _root_.solution
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (s t : RootTask T C r) (hst : s.1 ≠ t.1) {v : V}
    (hv : v ∈ s.branch.vertices) :
    v ∉ t.branch.carrier := by
  change
    v ∈ (incidentBranch T r s.1 (Classical.choose s.2)).vertices at hv
  change
    v ∉ (incidentBranch T r t.1 (Classical.choose t.2)).carrier
  exact mem_incidentBranch_vertices_not_mem_sibling_carrier
    (T := T) r (Classical.choose s.2) (Classical.choose t.2) hst hv
end RootTask
end TreeStack
