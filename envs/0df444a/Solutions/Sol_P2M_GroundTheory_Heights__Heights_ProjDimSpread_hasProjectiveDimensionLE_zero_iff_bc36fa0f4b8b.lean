-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjDimSpread_hasProjectiveDimensionLE_zero_iff_bc36fa0f4b8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:52.839666+00:00
-- url     : https://prove2.me/submissions/eaab3f72-73eb-45ad-a5a8-7711bd787751

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjDimSpread

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open CategoryTheory
variable {R : Type} [CommRing R]
namespace GroundTheory.Heights₂.Heights
namespace ProjDimSpread
theorem _root_.solution (M : ModuleCat.{0} R) (S : Submonoid R) :
    HasProjectiveDimensionLE (M.localizedModule S) 0 ↔
      Module.Projective (Localization S) (LocalizedModule S M) := by
  rw [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
    ← IsProjective.iff_projective]
  exact ⟨fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S),
    fun _ ↦ Module.Projective.of_equiv (localizedModuleEquiv M S).symm⟩
end ProjDimSpread
end GroundTheory.Heights₂.Heights
