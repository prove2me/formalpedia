-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.stab_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:53:13.640361+00:00
-- url     : https://prove2.me/submissions/25c8b2f9-d7c3-4c5b-a224-6c3a3227e9f1

import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective
import Theorems.Thm_ReciprocityTheory_Coh_FiniteLevelCohomology_stab_mem_nhds


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
open ReciprocityTheory.Gal Topology
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution (M : TRep R G) [DiscreteTopology M.V] (m : M.V) : IsOpen (stab M m : Set G) :=
  Subgroup.isOpen_of_mem_nhds _ (FiniteLevelCohomology.stab_mem_nhds M m)
end ReciprocityTheory.Coh.ProcyclicCohomology
