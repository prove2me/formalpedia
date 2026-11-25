-- Prove2me | solution 1 for PI.FglPhSplit.Wk.simeqW_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:43.852125+00:00
-- url     : https://prove2.me/submissions/3baf3918-8052-4284-8bba-02d735f33302

import Definitions.Def_Formalism_PeriodIntegrals_FglPhSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Theorems.Thm_PI_FglPhSplit_Wk_coeff_expMv

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
open PI.FglPhSplit MvPowerSeries
namespace PI.FglPhSplit.Wk
theorem _root_.solution {K : Type} [Field K] (W : Subring K) {σ : Type} (f : MvPowerSeries σ K) :
    SimeqW W f f := by
  classical
  refine ⟨by simp, fun n => ?_⟩
  rw [sub_self, coeff_expMv]
  refine W.sum_mem fun k _ => ?_
  rcases k with _ | k
  · rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, MvPowerSeries.coeff_one]
    split_ifs
    · exact W.one_mem
    · exact W.zero_mem
  · simp
end PI.FglPhSplit.Wk
