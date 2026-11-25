-- Prove2me | solution 1 for PI.PhiCubeOfFactor.Wk.logMv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:58.358378+00:00
-- url     : https://prove2.me/submissions/c2bc3197-2034-403e-a156-6e3df0998c61

import Definitions.Def_Formalism_PeriodIntegrals_PhiCubeOfFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFactorIdentity_ExpMvEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PhiCubeOfFactor PI.PhiCubeOfFactor.Wk
open PI.PhiCubeOfFactor MvPowerSeries PI.FglShared
variable {p : ℕ} [Fact p.Prime]
namespace PI.PhiCubeOfFactor.Wk
theorem _root_.solution {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : logMv F = logS F := rfl
end PI.PhiCubeOfFactor.Wk
