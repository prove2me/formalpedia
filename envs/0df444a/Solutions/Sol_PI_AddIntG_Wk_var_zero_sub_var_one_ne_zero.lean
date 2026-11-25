-- Prove2me | solution 1 for PI.AddIntG.Wk.var_zero_sub_var_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:03.831896+00:00
-- url     : https://prove2.me/submissions/68eed017-7d9c-43c2-b1d0-7f57ce53ae5e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
  have hs : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]
    decide
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h0
  simp [MvPowerSeries.coeff_X, hs] at h1
end PI.AddIntG.Wk
