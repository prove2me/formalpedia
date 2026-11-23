-- Prove2me | solution 1 for PI.AddIntG.Wk.subst_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:41.93026+00:00
-- url     : https://prove2.me/submissions/b33b00c9-0b85-4fc2-8ac4-499a716d311e

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
theorem _root_.solution {a : MvPowerSeries (Fin 2) ℂ_[p]} (ha : PowerSeries.HasSubst a)
    {b : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha.const hb]
end PI.AddIntG.Wk
