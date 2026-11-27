-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_cokernel___cokernelCohomologyMapCoindCokernel_Iso_hom_9b2e3e080a3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:14.477054+00:00
-- url     : https://prove2.me/submissions/c3efd06b-4dd8-42a8-9034-e907496b5e86

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_LongExactSequence
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]
namespace GroundTheory.ProfCoh
theorem _root_.solution :
    cokernel.π (cohomologyMap (coindCokernelπ A) 0) ≫
      (cokernelCohomologyMapCoindCokernelπIso A).hom = coindδ A 0 :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (coindδ_zero_exact A).gIsCokernel WalkingParallelPair.one
end GroundTheory.ProfCoh
