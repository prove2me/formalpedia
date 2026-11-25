-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntermediateRingQuotLength_smul_top_eq_span_79ee9c715187
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:29.971834+00:00
-- url     : https://prove2.me/submissions/cbbdb862-f973-435a-b064-16ac4368bb3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntermediateRingQuotLength

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
universe u
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength
theorem _root_.solution {A : Type*} [CommRing A] (a : A) :
    (a • ⊤ : Submodule A A) = Ideal.span {a} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
end GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength
