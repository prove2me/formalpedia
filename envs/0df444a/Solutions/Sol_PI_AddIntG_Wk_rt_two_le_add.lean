-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_two_le_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:46.094746+00:00
-- url     : https://prove2.me/submissions/c962b565-9f7e-45e5-aa0d-464beaaa9660

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
variable {σ : Type*}
namespace PI.AddIntG.Wk
theorem _root_.solution {f g : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) (hg : 2 ≤ g.order) :
    2 ≤ (f + g).order := by
  refine MvPowerSeries.le_order fun d hd => ?_
  rw [map_add, MvPowerSeries.coeff_of_lt_order (hd.trans_le hf),
    MvPowerSeries.coeff_of_lt_order (hd.trans_le hg), add_zero]
end PI.AddIntG.Wk
