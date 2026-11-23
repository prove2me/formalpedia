-- Prove2me | solution 1 for PI.AddIntG.Wk.lamA_coeff_wser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:28.675469+00:00
-- url     : https://prove2.me/submissions/c270103a-5893-4f58-85e9-20fe7f3a7dd3

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
theorem _root_.solution (wq : PowerSeries ℂ_[p]) (n : ℕ) :
    PowerSeries.coeff n (wser wq) = if 3 ≤ n then PowerSeries.coeff (n - 3) wq else 0 := by
  simp [wser, PowerSeries.coeff_X_pow_mul']
end PI.AddIntG.Wk
