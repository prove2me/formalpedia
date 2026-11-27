-- Prove2me | solution 2 for P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_c7ea4c385cf8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:25.092338+00:00
-- url     : https://prove2.me/submissions/d77ecf5f-56d3-4661-a5ff-5ff96a209316

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_OrderScalars

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
variable {G M : Type} [Group G] [CommGroup M] (φ : G →* Monoid.End M)
namespace GroundTheory.ProfCoh
theorem _root_.solution (f : G → Additive M) :
    (d₁₂ (Rep.of (intRepOfMonoidEnd.{0} φ))).hom f = (d₁₂ (Rep.of (zRepOfMonoidEnd φ))).hom f :=
  rfl
end GroundTheory.ProfCoh
