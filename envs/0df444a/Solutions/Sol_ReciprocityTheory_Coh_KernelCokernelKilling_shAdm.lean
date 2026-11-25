-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.shAdm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:00.208061+00:00
-- url     : https://prove2.me/submissions/a53b4830-2dc2-48c7-b63b-d33f6b0eab78

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_admissible_of_discrete_topology
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_shI_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.KernelCokernelKilling
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (M : TRep R G) [DiscreteTopology M.V]
namespace ReciprocityTheory.Coh.KernelCokernelKilling
theorem _root_.solution : admitted (shIP M) (quotMk (shC M) _ (shI_stable M)) :=
  admissible_of_discrete_topology _ _ rfl rfl (shI_inj M)
    (LinearMap.exact_iff.2 (Submodule.ker_mkQ _)) (Submodule.mkQ_surjective _)
end ReciprocityTheory.Coh.KernelCokernelKilling
