-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_logA_one_5d3ec8a2de84
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.16143+00:00
-- url     : https://prove2.me/submissions/d7fa80bc-14fe-4f44-a3c7-5a97c7e4e43a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero

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
theorem _root_.solution : logA 𝔸 (1 : 𝔸) = 0 := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse_apply_image
  rw [exp_zero] at h
  exact h
end Formalism.BasicNotions.Examples₂.CD
