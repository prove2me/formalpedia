-- Prove2me | solution 1 for PI.FglPhSplit.Wk.addPreservesExpCongruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:22.762681+00:00
-- url     : https://prove2.me/submissions/30e94b61-de79-4837-bed1-1ea86a286f7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Theorems.Thm_PI_FglPhSplit_Wk_simeqW_add

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
theorem _root_.solution : S3 := by
  intro K _ _ W σ f g f' g' h h'
  exact simeqW_add h h'
end PI.FglPhSplit.Wk
