-- Prove2me | solution 1 for PI.FglPhSplit.Wk.simeqW_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:32.36781+00:00
-- url     : https://prove2.me/submissions/e863f40f-dd95-469f-b344-44c5fc036efd

import Definitions.Def_Formalism_PeriodIntegrals_FglPhSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development

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
theorem _root_.solution {K : Type} [Field K] {W : Subring K} {σ : Type} {f g f' g' : MvPowerSeries σ K}
    (h : SimeqW W f g) (hf : f = f') (hg : g = g') : SimeqW W f' g' := by
  subst hf hg
  exact h
end PI.FglPhSplit.Wk
