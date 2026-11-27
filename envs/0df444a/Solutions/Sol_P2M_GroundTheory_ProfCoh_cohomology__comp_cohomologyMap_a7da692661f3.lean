-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_cohomology__comp_cohomologyMap_a7da692661f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:00.209083+00:00
-- url     : https://prove2.me/submissions/d62cfc5d-36d3-4e97-900d-d4ffcb4e318f

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
theorem _root_.solution (f : A ⟶ B) (n : ℕ) :
    cohomologyπ A n ≫ cohomologyMap f n =
      HomologicalComplex.cyclesMap (cochainsMap f) n ≫ cohomologyπ B n :=
  HomologicalComplex.homologyπ_naturality _ _
end GroundTheory.ProfCoh
