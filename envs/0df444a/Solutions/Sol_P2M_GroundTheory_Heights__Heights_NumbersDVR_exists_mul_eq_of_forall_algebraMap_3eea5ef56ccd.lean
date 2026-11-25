-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_mul_eq_of_forall_algebraMap_3eea5ef56ccd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:17.435368+00:00
-- url     : https://prove2.me/submissions/314d0af4-ca10-4c78-b615-42a44955af97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart

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
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {B X : Type*} [CommRing B] [CommRing X] (W : Ideal B) [W.IsPrime]
    (φ : X →+* Localization.AtPrime W) (h : ∀ z, ∃ a, φ a = algebraMap B (Localization.AtPrime W) z)
    (d : Localization.AtPrime W) :
    ∃ a b, φ b ∉ IsLocalRing.maximalIdeal (Localization.AtPrime W) ∧ φ b * d = φ a := by
  obtain ⟨⟨z, s⟩, hzs⟩ := IsLocalization.surj W.primeCompl d
  obtain ⟨a, ha⟩ := h z
  obtain ⟨b, hb⟩ := h s
  refine ⟨a, b, ?_, ?_⟩
  · rw [hb, IsLocalization.AtPrime.to_map_mem_maximal_iff _ W]
    exact s.2
  · rw [hb, ha, mul_comm]
    exact hzs
end GroundTheory.Heights₂.Heights.NumbersDVR
