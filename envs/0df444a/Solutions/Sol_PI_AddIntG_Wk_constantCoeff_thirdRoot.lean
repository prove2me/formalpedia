-- Prove2me | solution 1 for PI.AddIntG.Wk.constantCoeff_thirdRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:49.577735+00:00
-- url     : https://prove2.me/submissions/f284cc22-ad98-4199-b628-787de329f93f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_order_Bcf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
section order
variable {σ : Type*}
end order
private theorem rt_constantCoeff_lam_lemma {f : MvPowerSeries (Fin 2) ℂ_[p]} (hf : 2 ≤ f.order) :
    MvPowerSeries.constantCoeff f = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ hf
  simp
end PI.AddIntG.Wk
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Z3 W wq) = 0 := by
  simp [Z3, rt_constantCoeff_lam_lemma (rt_order_Bcf W wq)]
end PI.AddIntG.Wk
