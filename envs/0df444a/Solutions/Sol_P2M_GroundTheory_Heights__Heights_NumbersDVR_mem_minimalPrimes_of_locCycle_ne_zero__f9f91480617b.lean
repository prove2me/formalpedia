-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_locCycle_ne_zero__f9f91480617b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:43.760797+00:00
-- url     : https://prove2.me/submissions/8c9d8560-b2c4-4de9-809c-f825cf3c77a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalCoeffLocal

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
open ReciprocityTheory.ChartRestriction.G.AI
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dif_neg hc])
end GroundTheory.Heights₂.Heights.NumbersDVR
