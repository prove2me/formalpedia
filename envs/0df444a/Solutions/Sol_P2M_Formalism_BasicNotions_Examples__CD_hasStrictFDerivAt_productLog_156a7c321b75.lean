-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_productLog_156a7c321b75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:26.379859+00:00
-- url     : https://prove2.me/submissions/d06bfd0d-79c2-4a7b-a1cd-12c465812d1a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrict_mul_b9d1a3e90d30

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution : HasStrictFDerivAt (F2 (𝔸 := 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := hasStrict_mul (ContinuousLinearMap.fst ℝ 𝔸 𝔸) (ContinuousLinearMap.snd ℝ 𝔸 𝔸)
end Formalism.BasicNotions.Examples₂.CD
