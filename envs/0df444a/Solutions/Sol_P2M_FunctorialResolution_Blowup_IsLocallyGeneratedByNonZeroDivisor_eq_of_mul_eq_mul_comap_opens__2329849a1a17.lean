-- Prove2me | solution 1 for P2M_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_eq_of_mul_eq_mul_comap_opens__2329849a1a17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:50:49.396352+00:00
-- url     : https://prove2.me/submissions/45ddf457-ad3d-4b00-9729-4f44f89a2641

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_eq_of_mul_eq_mul
import Theorems.Thm_P2M_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_comap_opens__4171055502be

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
variable {Y : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
namespace _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution {F : Y.IdealSheafData}
    (hF : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor F) (U : Y.Opens) {J J' : U.toScheme.IdealSheafData}
    (h : F.comap U.ι * J = F.comap U.ι * J') : J = J' :=
  (hF.comap_opensι U).eq_of_mul_eq_mul h
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
