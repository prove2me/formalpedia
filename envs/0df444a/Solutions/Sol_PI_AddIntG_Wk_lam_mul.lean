-- Prove2me | solution 1 for PI.AddIntG.Wk.lam_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:27.168156+00:00
-- url     : https://prove2.me/submissions/3ec35471-8a63-464d-8531-2b2e221c7138

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_lam
import Theorems.Thm_PI_AddIntG_Wk_coeff_wSeriesVar_zero
import Theorems.Thm_PI_AddIntG_Wk_coeff_wSeriesVar_one
import Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_mul_X

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
theorem _root_.solution (wq : PowerSeries ℂ_[p]) :
    (Xv 1 - Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * lam wq = wv wq 1 - wv wq 0 := by
  ext e
  rw [sub_mul, map_sub, map_sub, mul_comm (Xv 1), mul_comm (Xv 0), lamA_coeff_mul_X, lamA_coeff_mul_X,
    coeff_wSeriesVar_zero, coeff_wSeriesVar_one, lamA_coeff_lam, lamA_coeff_lam]
  have a1 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 0 = e 0 := by simp
  have a2 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 1 = e 1 - 1 := by simp
  have a3 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 0 = e 0 - 1 := by simp
  have a4 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 1 = e 1 := by simp
  rw [a1, a2, a3, a4]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0
  · simp [h0, h1]
  · have : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    simp [h0, h1, this]
  · have : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h2 : e 0 - 1 + 0 + 1 = e 0 := by omega
    simp [h0, h1, this, h2]
  · have h3 : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h4 : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    have h2 : e 0 - 1 + e 1 + 1 = e 0 + (e 1 - 1) + 1 := by omega
    simp [h0, h1, h3, h4, h2]
end PI.AddIntG.Wk
