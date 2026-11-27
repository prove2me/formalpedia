-- Prove2me | solution 1 for PI.JetsPhW.Inv.vInv_mul_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:15:47.970584+00:00
-- url     : https://prove2.me/submissions/d220f3ba-435e-4158-a5ff-3913e0e9868b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
import Theorems.Thm_PI_JetsPhW_Inv_wq_const
import Theorems.Thm_PI_JetsPhW_Inv_dX_eq_derivative

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
open PI PI.JetsPhW PI.JetsPhW.Inv
variable {p : ℕ} [Fact p.Prime]
namespace PI.JetsPhW.Inv
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    vInv W wq * omegaW W wq = 1 := by
  have hc := wq_const h
  simp only [IsWq] at h
  have hd : PowerSeries.derivative ℂ_[p] wq =
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (wq + PowerSeries.X * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ *
        (2 * PowerSeries.X * wq + PowerSeries.X ^ 2 * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ *
        (3 * PowerSeries.X ^ 2 * wq ^ 2 + 2 * PowerSeries.X ^ 3 * wq * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ *
        (4 * PowerSeries.X ^ 3 * wq ^ 2 + 2 * PowerSeries.X ^ 4 * wq * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ *
        (6 * PowerSeries.X ^ 5 * wq ^ 3 + 3 * PowerSeries.X ^ 6 * wq ^ 2 * PowerSeries.derivative ℂ_[p] wq) := by
    conv_lhs => rw [h]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
      PowerSeries.derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  have hden : PowerSeries.constantCoeff (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) ≠ 0 := by
    simp [hc]
    rw [map_ofNat]
    norm_num
  have key : vInv W wq * (-(2 : PowerSeries ℂ_[p]) * wq - PowerSeries.X * dX wq) =
      wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2) := by
    rw [dX_eq_derivative]
    simp only [vInv]
    linear_combination (-(PowerSeries.X : PowerSeries ℂ_[p])) * hd
  simp only [omegaW]
  rw [← mul_assoc, key, PowerSeries.mul_inv_cancel _ hden]
end PI.JetsPhW.Inv
