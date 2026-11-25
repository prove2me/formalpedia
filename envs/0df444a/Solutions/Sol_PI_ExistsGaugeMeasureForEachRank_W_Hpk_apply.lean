-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.Hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:43.830642+00:00
-- url     : https://prove2.me/submissions/e2715d4c-7aaf-41f5-a921-c2b51407b80e

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
theorem _root_.solution (p q : Fin (2 * r + 0 + 1)) :
    Hpk 0 r p q = if q = Fin.rev p then (if p = cI r then -1 else 1) else 0 := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [Hpk, Fin.ext_iff, Fin.val_rev, cI]
  split_ifs <;> first | rfl | (exfalso; omega)
end PI.ExistsGaugeMeasureForEachRank.W
