-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_wv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:52.482009+00:00
-- url     : https://prove2.me/submissions/e56cd201-c2c2-41c6-8e35-0b5059002f9d

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
theorem _root_.solution (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    wv wq i = (Xv i) ^ 3 * PowerSeries.subst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) wq := by
  have ha : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  unfold wv wser
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X ha]
end PI.AddIntG.Wk
