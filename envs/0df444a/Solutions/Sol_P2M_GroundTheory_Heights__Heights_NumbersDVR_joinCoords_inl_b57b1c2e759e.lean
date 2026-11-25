-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_joinCoords_inl_b57b1c2e759e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:43.547882+00:00
-- url     : https://prove2.me/submissions/1ba1452d-52bf-428a-91d4-a595b5fcf6ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback

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
theorem _root_.solution {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (k : K)
    (i : ι k) : joinCoords y y' ⟨Sum.inl k, i⟩ = y ⟨k, i⟩ := rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
