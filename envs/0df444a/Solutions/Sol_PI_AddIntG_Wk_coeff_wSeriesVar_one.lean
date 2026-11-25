-- Prove2me | solution 1 for PI.AddIntG.Wk.coeff_wSeriesVar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:51.923659+00:00
-- url     : https://prove2.me/submissions/1c7ef22a-d9b5-4cd9-8a9e-871d1e8cb50f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Theorems.Thm_PI_AddIntG_Wk_lamA_single1

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
theorem _root_.solution (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 1) = if e 0 = 0 then PowerSeries.coeff (e 1) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single1 e) rfl rfl
end PI.AddIntG.Wk
