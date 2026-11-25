-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_idealEquiv_apply_ed453f3bd221
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:10.374254+00:00
-- url     : https://prove2.me/submissions/91919564-7018-4dcb-9d31-8e4292f14af4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
theorem _root_.solution (W : Ideal (MRing ι₁ R)) :
    idealEquiv (R := R) σ W = W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) := rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
