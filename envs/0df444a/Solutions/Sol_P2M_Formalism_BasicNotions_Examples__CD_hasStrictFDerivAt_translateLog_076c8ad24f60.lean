-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_translateLog_076c8ad24f60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:28.189392+00:00
-- url     : https://prove2.me/submissions/4e7a2863-c18f-4cd7-ad7c-b14e8ca66a62

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
theorem _root_.solution : HasStrictFDerivAt (F1 (𝔸 := 𝔸)) (ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := by
  have h := hasStrict_mul (𝔸 := 𝔸) (-ContinuousLinearMap.fst ℝ 𝔸 𝔸)
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸)
  rw [neg_add_cancel_left] at h
  have hf : F1 (𝔸 := 𝔸) = fun p => logA 𝔸 (exp ((-ContinuousLinearMap.fst ℝ 𝔸 𝔸) p) *
      exp ((ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) p)) := by
    funext p
    simp [F1]
  rw [hf]
  exact h
end Formalism.BasicNotions.Examples₂.CD
