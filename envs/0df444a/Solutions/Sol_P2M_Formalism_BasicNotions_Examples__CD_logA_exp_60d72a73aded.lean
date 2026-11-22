-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_logA_exp_60d72a73aded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:37.589439+00:00
-- url     : https://prove2.me/submissions/608a12ac-26ee-415d-b5d3-aef5f9c62296

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
theorem _root_.solution : ∀ᶠ X in 𝓝 (0 : 𝔸), logA 𝔸 (exp X) = X := hasStrictFDerivAt_exp_zero_alt.eventually_left_inverse
end Formalism.BasicNotions.Examples₂.CD
