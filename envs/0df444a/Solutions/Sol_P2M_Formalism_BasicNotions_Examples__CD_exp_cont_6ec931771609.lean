-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_exp_cont_6ec931771609
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:59.072806+00:00
-- url     : https://prove2.me/submissions/c1c309ef-2bc0-4051-bcad-cd7f91e9f7ed

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
theorem _root_.solution : Continuous (exp : 𝔸 → 𝔸) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact NormedSpace.exp_continuous
end Formalism.BasicNotions.Examples₂.CD
