-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_ker_preimage___comp_of_isIso_852b3ee68910
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:48:58.939585+00:00
-- url     : https://prove2.me/submissions/666ea92f-79fb-49b1-a165-ffa636862df9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_IsoBlowupPushforward

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) :
    ((f ⁻¹ᵁ U).ι ≫ f).ker = U.ι.ker := by
  have : IsIso (AlgebraicGeometry.morphismRestrict f U) := inferInstance
  rw [← (isPullback_morphismRestrict f U).w]
  exact Scheme.Hom.ker_comp_of_isIso ..
end FunctorialResolution.EmbeddedResolution
