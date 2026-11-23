-- Prove2me | solution 1 for PI.AddIntG.Wk.Fch_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:52.01484+00:00
-- url     : https://prove2.me/submissions/63afdc3e-949d-42ce-8624-3b442c4a5b85

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists

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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    Fch W wq = MvPowerSeries.subst (bZ W wq) (Z3 W wq) := rfl
end PI.AddIntG.Wk
