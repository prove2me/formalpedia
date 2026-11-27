-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjDimSpread_proof_290c734e725d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:43.659922+00:00
-- url     : https://prove2.me/submissions/77d3658e-ad2f-44f7-8f06-a452c79995c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjDimSpread
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjDimSpread_spread_8b8fc0279bd0

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
theorem _root_.solution : ProjDimSpread.Statement := by
  intro R _ _ I P _ ℓ h
  have e : ∀ (Q : Ideal R) [Q.IsPrime], (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≅
      ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) :=
    fun Q _ ↦ (ProjDimSpread.quotientEquiv I Q).toModuleIso
  have hP : HasProjectiveDimensionLE
      ((ModuleCat.of R (R ⧸ I)).localizedModule P.primeCompl) ℓ :=
    hasProjectiveDimensionLT_of_iso (e P).symm (ℓ + 1)
  obtain ⟨g, hg, hQ⟩ := ProjDimSpread.spread P ℓ (ModuleCat.of R (R ⧸ I)) hP
  refine ⟨g, hg, fun Q _ hgQ ↦ ?_⟩
  have := hQ Q hgQ
  exact hasProjectiveDimensionLT_of_iso (e Q) (ℓ + 1)
end ProjDimSpread
end GroundTheory.Heights₂.Heights
