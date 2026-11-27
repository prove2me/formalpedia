-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_ker_comap___eq_ker_of_isIso_comp_7508c0c594b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:08.666576+00:00
-- url     : https://prove2.me/submissions/833ade08-ab1d-4d63-bc1a-c87b82fcc96b

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_eq_ker_of_isIso_comp
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker_comap___eq_ker_morphismRestrict_3254f25617a8

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
theorem _root_.solution {W T S : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) (n : S ⟶ V.toScheme) (e : S ⟶ (m ⁻¹ᵁ V).toScheme) [IsIso e]
    (h : e ≫ (m ∣_ V) = n) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker n := by
  rw [ker_comap_ι_eq_ker_morphismRestrict m V, ker_eq_ker_of_isIso_comp n (m ∣_ V) e h]
end FunctorialResolution.EmbeddedResolution
