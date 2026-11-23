-- Prove2me | solution 1 for P2M_PI_FglShared_expMv_subst__fa51dcff15ff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:54.804285+00:00
-- url     : https://prove2.me/submissions/d4599d57-0c32-4d2b-aaab-a018ff9cead1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Theorems.Thm_PI_FglPhSplit_Wk_expMv_eq_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglShared
open MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglShared
theorem _root_.solution {σ : Type} {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    {f : PowerSeries ℂ_[p]} (hf : MvPowerSeries.constantCoeff f = 0) :
    PI.FglPhSplit.expMv (PowerSeries.subst x f) = PowerSeries.subst x (PI.FglPhSplit.expMv f) := by
  have hxs : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf
  rw [PI.FglPhSplit.Wk.expMv_eq_subst (PowerSeries.constantCoeff_subst_eq_zero hx f hf),
    PI.FglPhSplit.Wk.expMv_eq_subst hf, PowerSeries.subst_comp_subst_apply hfs hxs]
end PI.FglShared
