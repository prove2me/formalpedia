-- Prove2me | solution 1 for PI.AddIntG.Wk.lamA_coeff_lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:07.758801+00:00
-- url     : https://prove2.me/submissions/0311ca0e-7230-444f-ac50-ffdcfb2145bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero

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
    MvPowerSeries.coeff e (lam wq) = PowerSeries.coeff (e 0 + e 1 + 1) (wser wq) := rfl
end PI.AddIntG.Wk
