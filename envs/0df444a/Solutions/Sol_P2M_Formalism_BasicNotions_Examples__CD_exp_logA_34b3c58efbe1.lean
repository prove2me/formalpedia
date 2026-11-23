-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_exp_logA_34b3c58efbe1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:15.988482+00:00
-- url     : https://prove2.me/submissions/9a1f205f-5b59-41d9-992d-0e90d5434ec3

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
theorem _root_.solution : ∀ᶠ h in 𝓝 (1 : 𝔸), exp (logA 𝔸 h) = h := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).eventually_right_inverse
  rw [exp_zero] at h
  exact h
end Formalism.BasicNotions.Examples₂.CD
