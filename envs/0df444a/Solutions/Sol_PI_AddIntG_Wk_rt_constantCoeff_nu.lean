-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_constantCoeff_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:14.892987+00:00
-- url     : https://prove2.me/submissions/2a04af20-d8f6-4af9-9e1c-40d72d017d1d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_order_nu
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
theorem _root_.solution (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (nu wq) = 0 := by
  exact rt_constantCoeff_lam_lemma (rt_order_nu wq)
end PI.AddIntG.Wk
