-- Prove2me | solution 1 for PI.FglShared.subst_subst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:25.486835+00:00
-- url     : https://prove2.me/submissions/5bba9d78-43c2-47b6-ab8d-b907bd933e94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg

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
theorem _root_.solution {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) : PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy', hinv, PowerSeries.subst_X hy']
end PI.FglShared
