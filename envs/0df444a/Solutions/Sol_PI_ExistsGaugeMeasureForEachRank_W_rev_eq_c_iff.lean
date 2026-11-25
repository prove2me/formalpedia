-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.rev_eq_c_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:15:25.428234+00:00
-- url     : https://prove2.me/submissions/e675e72b-9cf1-4507-898b-d24e9262d85c

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
theorem _root_.solution (p : Fin (2 * r + 0 + 1)) : Fin.rev p = cI r ↔ p = cI r := by
  rw [Fin.ext_iff, Fin.ext_iff, Fin.val_rev]
  simp only [cI]
  have := p.isLt
  omega
end PI.ExistsGaugeMeasureForEachRank.W
