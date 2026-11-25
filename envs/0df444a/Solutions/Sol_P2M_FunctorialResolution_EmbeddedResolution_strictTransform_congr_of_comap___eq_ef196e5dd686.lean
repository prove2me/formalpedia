-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_strictTransform_congr_of_comap___eq_ef196e5dd686
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:29.880444+00:00
-- url     : https://prove2.me/submissions/e77520b4-67e7-403f-9b67-70cc8ad2683d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_OpenImmersionAppLE
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ReducedSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_strictTransform_eq_ker_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ D₂ : X.IdealSheafData)
    (h : D₁.comap (Scheme.Opens.ι W.support.compl) =
      D₂.comap (Scheme.Opens.ι W.support.compl)) :
    Blowup.strictTransform f W D₁ = Blowup.strictTransform f W D₂ := by
  rw [strictTransform_eq_ker_restrict f W D₁, strictTransform_eq_ker_restrict f W D₂, h]
end FunctorialResolution.EmbeddedResolution
