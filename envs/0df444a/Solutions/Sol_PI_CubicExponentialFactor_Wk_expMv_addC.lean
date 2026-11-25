-- Prove2me | solution 1 for PI.CubicExponentialFactor.Wk.expMv_addC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:57.200024+00:00
-- url     : https://prove2.me/submissions/03fc004c-54a9-4f87-923c-5d8145d32d26

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_ExpMvAddC
import Theorems.Thm_P2M_PI_FglShared_expMv_add__f0eb8b5a05d0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CubicExponentialFactor PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor MvPowerSeries PI.FglShared
set_option linter.unusedSimpArgs false
variable {p : ℕ} [Fact p.Prime]
namespace PI.CubicExponentialFactor.Wk
theorem _root_.solution {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
  exact PI.FglShared.expMv_add' hf hg
end PI.CubicExponentialFactor.Wk
