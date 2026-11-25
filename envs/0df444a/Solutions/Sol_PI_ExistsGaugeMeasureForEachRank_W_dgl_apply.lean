-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.dgl_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:29.960068+00:00
-- url     : https://prove2.me/submissions/bea48182-b644-4329-929c-7af378182115

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (u : ℂ) (i j : Fin (2 * r + 0 + 1)) :
    dgl r u i j = if i = j then (if i = cI r then u else 1) else 0 := by
  unfold dgl
  rw [Matrix.diagonal_apply]
end PI.ExistsGaugeMeasureForEachRank.W
