-- Prove2me | solution 1 for PI.PhiCubeOfFactor.Wk.expMv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:32.880647+00:00
-- url     : https://prove2.me/submissions/a2964636-74fa-4d75-86df-92093b3783a1

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
theorem _root_.solution {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : expMv F = PI.FglPhSplit.expMv F := rfl
end PI.PhiCubeOfFactor.Wk
