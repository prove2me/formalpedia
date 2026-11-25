-- Prove2me | solution 1 for P2M_PI_FglShared_expMv_add__f0eb8b5a05d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:31.227967+00:00
-- url     : https://prove2.me/submissions/0bef04c1-93e7-4dec-9341-f4ba2ed62739

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
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
open PI PI.FglShared
open MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglShared
theorem _root_.solution {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : PI.FglPhSplit.expMv (f + g) = PI.FglPhSplit.expMv f * PI.FglPhSplit.expMv g :=
  PI.FglPhSplit.Wk.expMv_add hf hg
end PI.FglShared
