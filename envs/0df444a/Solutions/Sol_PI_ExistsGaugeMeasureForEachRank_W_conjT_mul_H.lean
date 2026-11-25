-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.conjT_mul_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:51.451816+00:00
-- url     : https://prove2.me/submissions/3b4e5483-79b3-4acf-b74e-d8bafb0bf9ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_col_fix

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
theorem _root_.solution {g : Mat 0 r} (hg : g ∈ UWb 0 r) (p : Fin (2 * r + 0 + 1)) (hp : p ≠ cI r)
    (k : Fin (2 * r + 0 + 1)) : (gᴴ * Hpk 0 r) p k = Hpk 0 r p k := by
  simp [Matrix.mul_apply, col_fix hg p hp]
end PI.ExistsGaugeMeasureForEachRank.W
