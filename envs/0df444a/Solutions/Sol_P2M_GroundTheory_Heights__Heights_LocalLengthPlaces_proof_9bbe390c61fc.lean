-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalLengthPlaces_proof_9bbe390c61fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:40.244502+00:00
-- url     : https://prove2.me/submissions/09e1229e-0584-4646-9084-df785539443b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalLengthPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalQuotCard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredPlacesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightLocalQuotCentred
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRingQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PLocalLengthPlaces

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
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace LocalLengthPlaces
theorem _root_.solution (hC : LocalQuotCard.Statement) (hF : CentredPlacesFinite.Statement)
    (hE : LocalQuotCentred.Statement) (hP : PlacesRingQuot.Statement) :
    LocalLengthPlaces.Statement := by
  intro L _ _ O hft hfr m _ f hf
  have hfS : (f : L) ∈ placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} :=
    fun w hw ↦ hw.1 f
  have hg : (⟨f, hfS⟩ : placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}) ≠ 0 :=
    fun h ↦ hf (Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [← Real.log_pow, ← Nat.cast_pow, ← hC L O hft hfr m f hf, hE L O hft hfr m f hf ⟨f, hfS⟩ rfl]
  exact hP L _ (hF L O hft hfr m) ⟨f, hfS⟩ hg
end LocalLengthPlaces
end GroundTheory.Heights₂.Heights
