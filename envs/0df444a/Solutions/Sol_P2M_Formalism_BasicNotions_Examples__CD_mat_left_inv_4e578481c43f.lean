-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_mat_left_inv_4e578481c43f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:32:28.176254+00:00
-- url     : https://prove2.me/submissions/5e2379e5-075b-4129-a7f1-3372a62045a2

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
theorem _root_.solution (g : UpqT P Q) : (J * (UpqT.mat g)ᴴ * J) * UpqT.mat g = 1 := by
  have h := mat_mem P Q g
  calc J * (UpqT.mat g)ᴴ * J * UpqT.mat g = J * ((UpqT.mat g)ᴴ * J * UpqT.mat g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, J_sq]
end Formalism.BasicNotions.Examples₂.CD
