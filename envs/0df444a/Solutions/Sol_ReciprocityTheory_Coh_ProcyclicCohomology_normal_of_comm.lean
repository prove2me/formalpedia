-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.normal_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:33.175222+00:00
-- url     : https://prove2.me/submissions/7dc96bb5-073b-49d0-9651-8627e6523711

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot

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
theorem _root_.solution (hc : ∀ a b : G, a * b = b * a) (W : Subgroup G) : W.Normal :=
  ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
end ReciprocityTheory.Coh.ProcyclicCohomology
