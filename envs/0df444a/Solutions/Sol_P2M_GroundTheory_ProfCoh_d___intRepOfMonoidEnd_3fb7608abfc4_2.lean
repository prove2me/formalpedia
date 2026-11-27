-- Prove2me | solution 2 for P2M_GroundTheory_ProfCoh_d___intRepOfMonoidEnd_3fb7608abfc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:13:19.30637+00:00
-- url     : https://prove2.me/submissions/d242b4e3-d86e-45d9-87c1-352aaec81a00

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
    (d₂₃ (Rep.of (intRepOfMonoidEnd.{0} φ))).hom f = (d₂₃ (Rep.of (zRepOfMonoidEnd φ))).hom f :=
  rfl
end GroundTheory.ProfCoh
