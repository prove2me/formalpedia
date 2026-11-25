-- Prove2me | solution 1 for PI.AddIntG.Wk.var_zero_sub_var_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:57.203318+00:00
-- url     : https://prove2.me/submissions/fdde63e5-1480-4b3d-83a3-751380f6e71a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe

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
  intro h
  have h2 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro hs
    have h3 := congrArg (fun f => f 0) hs
    simp at h3
  simp [Xv, MvPowerSeries.coeff_X, hne] at h2
end PI.AddIntG.Wk
