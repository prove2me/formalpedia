-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_joinForm_mem_pointIdeal_iff_ec545b5ede48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:14.359133+00:00
-- url     : https://prove2.me/submissions/7310358a-a2da-416d-9d8a-c65a2916cb9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pointConeMap_joinCoords_joinForm_b2442480fdad

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
variable {K K' : Type} {ι : K → Type} {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    joinForm f ∈ pointIdeal R (joinCoords y y') ↔ f ∈ pointIdeal R y := by
  simp only [pointIdeal, RingHom.mem_ker, pointConeMap_joinCoords_joinForm]
  exact map_eq_zero_iff _ (rename_injective _ Sum.inl_injective)
end GroundTheory.Heights₂.Heights.NumbersDVR
