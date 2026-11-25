-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_saturated_e97d455e1e91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:46.55349+00:00
-- url     : https://prove2.me/submissions/ada0a931-527d-4e3b-9091-61ab44abfbce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtPrimeAtMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultAtOfSaturated

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
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) : Q ∈ J.minimalPrimes := by
  refine ⟨⟨‹Q.IsPrime›, hJQ⟩, fun W hW hWQ q hq => ?_⟩
  obtain ⟨s, hs, hsq⟩ := hsat q hq
  exact (hW.1.mem_or_mem (hW.2 hsq)).resolve_left (fun h => hs (hWQ h))
end GroundTheory.Heights₂.Heights.NumbersDVR
