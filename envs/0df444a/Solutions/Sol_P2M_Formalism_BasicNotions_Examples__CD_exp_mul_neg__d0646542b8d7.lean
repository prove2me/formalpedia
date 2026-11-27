-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_exp_mul_neg__d0646542b8d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:24.632507+00:00
-- url     : https://prove2.me/submissions/1353f347-443a-41a7-9eb5-b2b5f9e9d39f

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero

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
open MeasureTheory Filter Topology Metric NormedSpace Set Matrix Formalism.UG.P
open scoped ENNReal NNReal Matrix.Norms.Operator
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (X : MM P Q) : exp X * exp (-X) = 1 := by
  have h := NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl X))
  rw [add_neg_cancel, NormedSpace.exp_zero] at h
  exact h.symm
end Formalism.BasicNotions.Examples₂.CD
