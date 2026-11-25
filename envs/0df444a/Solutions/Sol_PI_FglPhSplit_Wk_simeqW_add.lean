-- Prove2me | solution 1 for PI.FglPhSplit.Wk.simeqW_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:06.909956+00:00
-- url     : https://prove2.me/submissions/77f6950a-1ddf-46d3-a9b3-74ae53031bd3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Theorems.Thm_PI_FglPhSplit_Wk_expMv_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries Finset
variable {K : Type} [Field K] {σ : Type}
namespace PI.FglPhSplit.Wk
theorem _root_.solution [CharZero K] {W : Subring K} {f g f' g' : MvPowerSeries σ K}
    (h : SimeqW W f g) (h' : SimeqW W f' g') : SimeqW W (f + f') (g + g') := by
  classical
  obtain ⟨h0, hW⟩ := h
  obtain ⟨h0', hW'⟩ := h'
  have e : f + f' - (g + g') = (f - g) + (f' - g') := by ring
  refine ⟨by rw [e, map_add, h0, h0', add_zero], fun n => ?_⟩
  rw [e, expMv_add h0 h0', coeff_mul]
  exact W.sum_mem fun p _ => W.mul_mem (hW _) (hW' _)
end PI.FglPhSplit.Wk
