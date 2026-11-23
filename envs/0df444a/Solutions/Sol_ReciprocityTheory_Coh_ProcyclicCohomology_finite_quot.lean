-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:32.609955+00:00
-- url     : https://prove2.me/submissions/abcb6f22-d5aa-441c-a0e0-5beee681d55f

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
theorem _root_.solution [CompactSpace G] (hc : ∀ a b : G, a * b = b * a) {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Finite (G ⧸ W) := by
  exact Subgroup.quotient_finite_of_isOpen W hW
end ReciprocityTheory.Coh.ProcyclicCohomology
