-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.index_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:43.753678+00:00
-- url     : https://prove2.me/submissions/a13b33f1-17c3-4c6b-9072-a39ae8c1001b

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_finite_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.ProcyclicCohomology
open Topology
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : 0 < W.index := by
  haveI := finite_quot hc hW
  exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
end ReciprocityTheory.Coh.ProcyclicCohomology
