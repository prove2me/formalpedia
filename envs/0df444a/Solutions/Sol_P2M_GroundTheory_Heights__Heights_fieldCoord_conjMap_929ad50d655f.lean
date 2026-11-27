-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fieldCoord_conjMap_929ad50d655f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:10:54.320085+00:00
-- url     : https://prove2.me/submissions/e90e7079-dc0b-438f-9145-d946a0058423

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples

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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (σ : K →+* ℂ) (t : Fibre σ K) :
    fieldCoord (conjugate σ) (conjMap σ K t) = starRingEnd ℂ (fieldCoord σ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z x =>
    rw [conjMap_tmul, fieldCoord_tmul, fieldCoord_tmul, map_mul]
    rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
end GroundTheory.Heights₂.Heights
