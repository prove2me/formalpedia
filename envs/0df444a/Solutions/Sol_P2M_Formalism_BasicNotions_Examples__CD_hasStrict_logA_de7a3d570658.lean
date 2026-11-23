-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_hasStrict_logA_de7a3d570658
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:16.369798+00:00
-- url     : https://prove2.me/submissions/025a99e0-8abb-4625-8c26-cfc6b6bb7d58

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
theorem _root_.solution : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (1 : 𝔸) := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).to_localInverse
  rw [exp_zero] at h
  exact h
end Formalism.BasicNotions.Examples₂.CD
