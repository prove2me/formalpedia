-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FglPtW.log_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:16.581543+00:00
-- url     : https://prove2.me/submissions/9e8f1dfb-d93e-4576-8ba0-d6127c65853f

import Definitions.Def_Formalism_PeriodIntegrals_FglPtW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupPoints_ConstantCoeffLogEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FglPtW
open PI.FglPtW
namespace PI.UnitaryGroupMassFormula.FglPtW
theorem _root_.solution {K : Type} [CommRing K] {l ex : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ex = 0) (hlex : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type} (y : MvPowerSeries σ K) (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hy' : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  rw [← PowerSeries.subst_comp_subst_apply hex hy', hlex, PowerSeries.subst_X hy']
end PI.UnitaryGroupMassFormula.FglPtW
