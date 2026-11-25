-- Prove2me | solution 1 for PI.WfLogWork.omega_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:40.168681+00:00
-- url     : https://prove2.me/submissions/dff3b028-14e9-4f35-a9fb-9153a352392d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
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
open PI PI.WfLogWork
open PI.ExpIntWProof PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.WfLogWork
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hW : AddIntG.IsWq W wq) :
    AddIntG.omegaW W wq = (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq))⁻¹ := by
  have h := omega_mul_Gv hW
  have hc : PowerSeries.constantCoeff (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)) ≠ 0 := by
    intro h0
    have e := congrArg PowerSeries.constantCoeff h
    rw [map_mul, map_neg, map_one] at e
    rw [map_neg, neg_eq_zero] at h0
    rw [h0, mul_zero] at e
    exact one_ne_zero (neg_eq_zero.1 e.symm)
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc, mul_neg, h, neg_neg]
end PI.WfLogWork
