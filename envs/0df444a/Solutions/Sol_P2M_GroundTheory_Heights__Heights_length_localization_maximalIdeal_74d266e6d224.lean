-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_localization_maximalIdeal_74d266e6d224
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:42:41.459977+00:00
-- url     : https://prove2.me/submissions/bd2f8383-61db-4bf0-a82b-5d00a6bad9ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters

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
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (B : Type u) [CommRing B] [IsLocalRing B] :
    Module.length (Localization.AtPrime (maximalIdeal B)) (Localization.AtPrime (maximalIdeal B)) =
      Module.length B B := by
  have hU : (maximalIdeal B).primeCompl ≤ IsUnit.submonoid B := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.1 hs
  let e := IsLocalization.atUnits B (maximalIdeal B).primeCompl
    (S := Localization.AtPrime (maximalIdeal B)) hU
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime (maximalIdeal B))) :=
    e.surjective
  rw [← Module.length_eq_of_surjective (S := B) hsurj]
  exact e.toLinearEquiv.length_eq.symm
end GroundTheory.Heights₂.Heights
