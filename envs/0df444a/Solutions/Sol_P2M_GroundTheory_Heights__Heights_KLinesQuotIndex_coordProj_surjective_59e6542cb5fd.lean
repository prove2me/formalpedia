-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_coordProj_surjective_59e6542cb5fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:42.008032+00:00
-- url     : https://prove2.me/submissions/77b6e2a9-9f18-409c-992a-910b5e27992d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesQuotIndex

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
open GroundTheory.Heights₂.Heights.KLinesQuotIndex
namespace GroundTheory.Heights₂.Heights.KLinesQuotIndex
theorem _root_.solution {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) : Function.Surjective (coordProj B) :=
  (LinearMap.funLeft_surjective_of_injective K K Sum.inr Sum.inr_injective).comp
    B.equivFun.surjective
end GroundTheory.Heights₂.Heights.KLinesQuotIndex
