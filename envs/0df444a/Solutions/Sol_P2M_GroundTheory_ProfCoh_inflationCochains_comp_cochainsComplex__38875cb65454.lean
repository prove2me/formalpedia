-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_inflationCochains_comp_cochainsComplex__38875cb65454
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:20:39.855798+00:00
-- url     : https://prove2.me/submissions/a74b86f4-2367-4e63-8c22-6fd5dddc2720

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitDefs

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
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable (A : Rep.{u} k G)
variable [IsTopologicalGroup G] [IsDiscreteRep A]
namespace GroundTheory.ProfCoh
theorem _root_.solution (U : OpenNormalSubgroup G) :
    inflationCochains A U ≫ cochainsComplexι A = infCochains A U := by
  ext n : 1
  exact inflationCochainsX_comp_ι A U n
end GroundTheory.ProfCoh
