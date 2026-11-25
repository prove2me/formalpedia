-- Prove2me | solution 1 for PI.AddIntG.Wk.dv_pderiv_subst_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:46.920061+00:00
-- url     : https://prove2.me/submissions/4a5a2978-2be1-4719-9075-004ddf03b35a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder

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
theorem _root_.solution {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (P : Polynomial R) (i : σ) :
    MvPowerSeries.pderiv R i (PowerSeries.subst a (P : PowerSeries R)) =
      PowerSeries.subst a (PowerSeries.derivative R (P : PowerSeries R)) * MvPowerSeries.pderiv R i a := by
  rw [PowerSeries.derivative_coe, PowerSeries.subst_coe ha, PowerSeries.subst_coe ha,
    Derivation.comp_aeval_eq, smul_eq_mul]
end PI.AddIntG.Wk
