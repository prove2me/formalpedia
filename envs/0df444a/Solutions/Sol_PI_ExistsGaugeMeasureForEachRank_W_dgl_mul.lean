-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.dgl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:03.740502+00:00
-- url     : https://prove2.me/submissions/57f8c8e5-80a5-401d-b1fe-c0db69533f9a

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
theorem _root_.solution (u v : ℂ) : dgl r u * dgl r v = dgl r (u * v) := by
  simp only [dgl, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp
end PI.ExistsGaugeMeasureForEachRank.W
