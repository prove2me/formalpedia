-- Prove2me | solution 1 for PI.AddIntG.Wk.subst_thirdRoot_wSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:55.093346+00:00
-- url     : https://prove2.me/submissions/0fa88abb-a839-4d08-811e-4694fa439e92

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_constantCoeff_lam
import Theorems.Thm_PI_AddIntG_Wk_rt_constantCoeff_nu
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_thirdRoot
import Theorems.Thm_PI_AddIntG_Wk_zwEquation_thirdRoot
import Theorems.Thm_PI_AddIntG_Wk_rt_G_map
import Theorems.Thm_PI_AddIntG_Wk_G_wser


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
    PowerSeries.subst (Z3 W wq) (wser wq) = lam wq * Z3 W wq + nu wq := by
  obtain ⟨z, hz⟩ : ∃ z, z = Z3 W wq := ⟨_, rfl⟩
  have hGv := zwEquation_thirdRoot h
  rw [← hz] at hGv ⊢
  have hz0 : MvPowerSeries.constantCoeff z = 0 := by rw [hz]; exact constantCoeff_thirdRoot W wq
  have ha : PowerSeries.HasSubst z := PowerSeries.HasSubst.of_constantCoeff_zero hz0
  obtain ⟨w, hw⟩ : ∃ w, w = PowerSeries.subst z (wser wq) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = lam wq * z + nu wq := ⟨_, rfl⟩
  rw [← hw, ← hv]
  rw [← hv] at hGv
  have hGw : G W z w = 0 := by
    have h0 := congrArg (PowerSeries.substAlgHom ha) (G_wser h)
    rw [rt_G_map, map_zero, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X ha, ← hw] at h0
    exact h0
  have hw' : w = z ^ 3 * PowerSeries.subst z wq := by
    rw [hw, wser, ← PowerSeries.coe_substAlgHom ha, map_mul, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X ha]
  have hw0 : MvPowerSeries.constantCoeff w = 0 := by
    rw [hw', map_mul, map_pow, hz0]
    simp
  have hv0 : MvPowerSeries.constantCoeff v = 0 := by
    simp [hv, hz0, rt_constantCoeff_lam, rt_constantCoeff_nu]
  have hfac : G W z v - G W z w = (v - w) *
      (algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₁ * z +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₂ * z ^ 2 +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₃ * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₄ * z * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₆ * (v ^ 2 + v * w + w ^ 2) - 1) := by
    unfold G
    ring
  have hF : (algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₁ * z +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₂ * z ^ 2 +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₃ * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₄ * z * (v + w) +
        algebraMap ℂ_[p] (MvPowerSeries (Fin 2) ℂ_[p]) W.a₆ * (v ^ 2 + v * w + w ^ 2) - 1) ≠ 0 := by
    intro h0
    have h1 := congrArg MvPowerSeries.constantCoeff h0
    simp [hz0, hv0, hw0] at h1
  rw [hGv, hGw, sub_zero] at hfac
  exact (sub_eq_zero.1 ((mul_eq_zero.1 hfac.symm).resolve_right hF)).symm
end PI.AddIntG.Wk
