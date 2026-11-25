-- Prove2me | solution 1 for PI.AddIntG.Wk.omega_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:14.944199+00:00
-- url     : https://prove2.me/submissions/e6e0f651-a53e-41ca-bde9-e3d7aad4b3b5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Theorems.Thm_PI_AddIntG_Wk_Gv_algHom
import Theorems.Thm_PI_AddIntG_Wk_omega_mul_Gv


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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {r : MvPowerSeries (Fin 2) ℂ_[p]} (hr : MvPowerSeries.constantCoeff r = 0) :
    PowerSeries.subst r (omegaW W wq) * Gv W r (PowerSeries.subst r (wser wq)) = -1 := by
  have hs : PowerSeries.HasSubst r := PowerSeries.HasSubst.of_constantCoeff_zero hr
  have key := congrArg (PowerSeries.substAlgHom hs) (omega_mul_Gv h)
  rw [map_mul, Gv_algHom, map_neg, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hs] at key
  exact key
end PI.AddIntG.Wk
