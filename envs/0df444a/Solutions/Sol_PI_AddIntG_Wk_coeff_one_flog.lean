-- Prove2me | solution 1 for PI.AddIntG.Wk.coeff_one_flog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:08.1778+00:00
-- url     : https://prove2.me/submissions/87ce5f9e-1632-440c-86e7-a4c518b0988b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar

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
    PowerSeries.coeff 1 (flog W wq) = 1 := by
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := h
  have hw : PowerSeries.constantCoeff wq = 1 := by
    rw [h']
    simp
  have h2 : (2 : ℂ_[p]) ≠ 0 := by
    first
    | exact two_ne_zero
    | (intro h2z
       have hinj := (algebraMap ℚ_[p] ℂ_[p]).injective
       have h22 : algebraMap ℚ_[p] ℂ_[p] 2 = algebraMap ℚ_[p] ℂ_[p] 0 := by
         rw [map_ofNat, map_zero]; exact h2z
       exact two_ne_zero (hinj h22))
  have hinv : PowerSeries.constantCoeff (PI.AddIntG.omegaW W wq) = 1 := by
    have hc2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
    simp [PI.AddIntG.omegaW, hw, PowerSeries.constantCoeff_inv, h2, hc2]
    first
    | done
    | exact mul_inv_cancel₀ h2
    | field_simp
  have e : PowerSeries.coeff 1 (PI.AddIntG.flog W wq) = PowerSeries.coeff 0 (PI.AddIntG.omegaW W wq) := by
    simp [PI.AddIntG.flog]
  first
  | (rw [e, PowerSeries.coeff_zero_eq_constantCoeff_apply, hinv])
  | (rw [e]; simpa using hinv)
  | simpa [e] using hinv
end PI.AddIntG.Wk
