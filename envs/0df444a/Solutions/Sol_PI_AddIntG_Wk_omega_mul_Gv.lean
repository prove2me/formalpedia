-- Prove2me | solution 1 for PI.AddIntG.Wk.omega_mul_Gv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:10.414609+00:00
-- url     : https://prove2.me/submissions/4ed18bb3-725a-4393-82ac-032aa02070a0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Theorems.Thm_PI_AddIntG_Wk_dX_eq_derivative
import Theorems.Thm_PI_AddIntG_Wk_wq_const


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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    omegaW W wq * Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) = -1 := by
  have hw1 := wq_const h
  have hder := dX_eq_derivative wq
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) * wq + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq ^ 2 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 6 * wq ^ 3 := h
  have hD := congrArg (PowerSeries.derivative ℂ_[p]) h'
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    PowerSeries.derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at hD
  have hQ : PowerSeries.constantCoeff
      (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2)) ≠ 0 := by
    have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := by
      rw [show (2 : PowerSeries ℂ_[p]) = 1 + 1 by norm_num, map_add, map_one]
      norm_num
    simp [hw1, h2]
  have key : (-(2 : PowerSeries ℂ_[p]) * wq - (PowerSeries.X : PowerSeries ℂ_[p]) * PowerSeries.derivative ℂ_[p] wq) *
      (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 + 2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) +
        2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) + 3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) ^ 2 - 1) =
      -(wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2)) := by
    linear_combination (PowerSeries.X : PowerSeries ℂ_[p]) * hD
  calc omegaW W wq * Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)
      = ((-(2 : PowerSeries ℂ_[p]) * wq - (PowerSeries.X : PowerSeries ℂ_[p]) * PowerSeries.derivative ℂ_[p] wq) *
        (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 + 2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) +
          2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) + 3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) ^ 2 - 1)) *
        (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2))⁻¹ := by
        simp only [omegaW, Gv, wser, hder]
        ring
    _ = -1 := by
        rw [key, neg_mul, PowerSeries.mul_inv_cancel _ hQ]
end PI.AddIntG.Wk
