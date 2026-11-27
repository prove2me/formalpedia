-- Prove2me | solution 1 for P2M_GroundTheory_ProfCoh_inflationCocone___app_aa39b7f56731
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:27.043324+00:00
-- url     : https://prove2.me/submissions/746e8aff-6508-4e39-b5a3-e648eccd4cb7

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
theorem _root_.solution (n : ℕ) (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (inflationCocone A n).ι.app U = inflation A U.unop n :=
  rfl
end GroundTheory.ProfCoh
