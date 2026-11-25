-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_exp_neg_mul_b0802c46782f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:31:01.16254+00:00
-- url     : https://prove2.me/submissions/01665506-25d8-4ba8-8b44-6978acf68184

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
theorem _root_.solution (X : 𝔸) : exp (-X) * exp X = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]
end Formalism.BasicNotions.Examples₂.CD
