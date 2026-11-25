-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.rho_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:07.816113+00:00
-- url     : https://prove2.me/submissions/4c4ce85b-f86a-48a8-a275-4f52b798e0b2

import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_GroupCohomology_ModelComparisonDegreeZeroBijective

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
theorem _root_.solution (M : TRep R G) (hc : ∀ a b : G, a * b = b * a) (a b : G) (x : M.V) :
    M.rho a (M.rho b x) = M.rho b (M.rho a x) := by
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
end ReciprocityTheory.Coh.ProcyclicCohomology
