-- Prove2me | solution 1 for PI.AddIntG.Wk.dX_eq_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:28.914956+00:00
-- url     : https://prove2.me/submissions/54c75dfe-60c7-4070-89bd-8a9c07c73787

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative

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
theorem _root_.solution (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring
end PI.AddIntG.Wk
