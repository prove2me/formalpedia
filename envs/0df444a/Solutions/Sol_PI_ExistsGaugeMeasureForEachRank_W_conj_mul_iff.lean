-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.conj_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:12:16.457954+00:00
-- url     : https://prove2.me/submissions/fe837c4f-b918-4d1f-9c17-e278e60f969e

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
theorem _root_.solution (u : ℂ) : (starRingEnd ℂ) u * u = 1 ↔ ‖u‖ = 1 := by
  rw [Complex.conj_mul']
  norm_cast
  exact pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero
end PI.ExistsGaugeMeasureForEachRank.W
