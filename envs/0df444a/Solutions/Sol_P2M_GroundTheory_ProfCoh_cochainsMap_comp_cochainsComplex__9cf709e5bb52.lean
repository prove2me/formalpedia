-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_cochainsMap_comp_cochainsComplex__9cf709e5bb52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:13.239397+00:00
-- url     : https://prove2.me/submissions/b4d7960c-9331-4bf2-8a10-e352ef0362d8

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality

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
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
namespace GroundTheory.ProfCoh
theorem _root_.solution (f : A ⟶ B) :
    cochainsMap f ≫ cochainsComplexι B =
      cochainsComplexι A ≫ groupCohomology.cochainsMap (MonoidHom.id G) f := by
  ext n c : 3
  rfl
end GroundTheory.ProfCoh
