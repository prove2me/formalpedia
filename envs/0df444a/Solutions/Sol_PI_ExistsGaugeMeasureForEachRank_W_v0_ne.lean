-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.v0_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:21.831413+00:00
-- url     : https://prove2.me/submissions/9139b24c-4443-45b4-8e6a-9888782c1ba9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_norm_v0_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution : v0 r ≠ 0 := by
  intro h
  have := norm_v0_eq_one (r := r)
  rw [h, norm_zero] at this
  exact zero_ne_one this
end PI.ExistsGaugeMeasureForEachRank.W
