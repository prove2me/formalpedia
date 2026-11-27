-- Prove2me | solution 2 for P2M_GroundTheory_ProfCoh_mem_coboundaries__intRepOfMonoidEnd_iff_8d7a2be120d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:16:58.194597+00:00
-- url     : https://prove2.me/submissions/bf491998-3161-48e0-9b7a-dac892931a0e

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
theorem _root_.solution (f : G × G → Additive M) :
    f ∈ coboundaries₂ (Rep.of (intRepOfMonoidEnd.{0} φ)) ↔
      f ∈ coboundaries₂ (Rep.of (zRepOfMonoidEnd φ)) :=
  Iff.rfl
end GroundTheory.ProfCoh
