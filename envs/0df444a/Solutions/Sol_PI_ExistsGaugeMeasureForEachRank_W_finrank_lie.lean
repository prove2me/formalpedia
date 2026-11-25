-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.finrank_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:45.215727+00:00
-- url     : https://prove2.me/submissions/e5329683-4dfe-43a3-af6b-a8836150d08b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_lieE_eq
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_v0_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution : Module.finrank ℝ (lieE (UWb 0 r)) = 1 := by
  rw [lieE_eq]; exact finrank_span_singleton v0_ne
end PI.ExistsGaugeMeasureForEachRank.W
