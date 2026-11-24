-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_ne_zero_8b01cdf8892a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:22.455473+00:00
-- url     : https://prove2.me/submissions/8c58bf16-ae91-4f2b-bc68-1d72e94eb580

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_index_ne_zero_0c8323a65fb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_ba0dcb3ccb8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_relIndex_map_subtype_1ba93abccb64


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
theorem _root_.solution [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {β : B} (hβ : β ≠ 0) :
    (B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup ≠ 0 := by
  rw [map_mul_eq, relIndex_map_subtype]
  exact index_ne_zero (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ)
end GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
