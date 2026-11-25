-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_chartLength_self_eq_of_ringEquiv_ed399607d5db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:25.149526+00:00
-- url     : https://prove2.me/submissions/42015c4c-b0b3-4a48-8f66-295655f6c8c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalChartLength

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
theorem _root_.solution {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  let _ := RingHomInvPair.of_ringEquiv τ
  let _ := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]
end GroundTheory.Heights₂.Heights.NumbersDVR
