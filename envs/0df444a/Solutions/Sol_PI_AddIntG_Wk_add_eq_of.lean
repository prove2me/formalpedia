-- Prove2me | solution 1 for PI.AddIntG.Wk.add_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:57.207977+00:00
-- url     : https://prove2.me/submissions/89a47b85-7fd1-4c0d-9f9f-689f5c6c6b94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Theorems.Thm_PI_AddIntG_Wk_flog_constantCoeff
import Theorems.Thm_PI_AddIntG_Wk_coeff_one_flog
import Theorems.Thm_PI_AddIntG_Wk_subst_left_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
private theorem hasSubst_of_constantCoeff_eq_zero_additive_integral_groups {K : Type*} [Field K] {a : PowerSeries K}
    (ha : PowerSeries.constantCoeff a = 0) : PowerSeries.HasSubst a := by
  have ha2 : MvPowerSeries.constantCoeff a = 0 := ha
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero ha2
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [ha2]; exact IsNilpotent.zero)
private theorem hasSubst_of_mvConstantCoeff_eq_zero {K : Type*} [Field K] {σ : Type*} {b : MvPowerSeries σ K}
    (hb : MvPowerSeries.constantCoeff b = 0) : PowerSeries.HasSubst b := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hb
  | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hb]; exact IsNilpotent.zero)
private theorem subst_subst_eq_subst_subst_of_constantCoeff {K : Type*} [Field K] {σ : Type*} {a : PowerSeries K}
    {b : MvPowerSeries σ K} (ha : PowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (f : PowerSeries K) :
    PowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (PowerSeries.subst b a) f := by
  have ha' := hasSubst_of_constantCoeff_eq_zero_additive_integral_groups ha
  have hb' := hasSubst_of_mvConstantCoeff_eq_zero hb
  first
  | exact PowerSeries.subst_comp_subst_apply ha' hb' f
  | exact PowerSeries.subst_comp_subst_apply (R := K) ha' hb' f
  | exact congrFun (PowerSeries.subst_comp_subst ha' hb') f
  | simp [PowerSeries.subst_comp_subst_apply ha' hb']
private theorem subst_X_eq_self_of_constantCoeff_eq_zero {K : Type*} [Field K] {σ : Type*} {b : MvPowerSeries σ K}
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst b (PowerSeries.X : PowerSeries K) = b := by
  have hb' := hasSubst_of_mvConstantCoeff_eq_zero hb
  first
  | exact PowerSeries.subst_X hb'
  | simp [PowerSeries.subst_X hb']
end PI.AddIntG.Wk
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (F : MvPowerSeries (Fin 2) ℂ_[p]) (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF : PowerSeries.subst F (flog W wq) =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq)) :
    add (flog W wq) ex (Xv 0) (Xv 1) = F := by
  have hl0 := flog_constantCoeff W wq
  have hl1 := coeff_one_flog h
  have hinv := subst_left_inv hl0 hl1 hex0 hex
  first
  | unfold PI.AddIntG.add
  | simp only [PI.AddIntG.add]
  rw [← hF, ← subst_subst_eq_subst_subst_of_constantCoeff hl0 hF0 ex, hinv, subst_X_eq_self_of_constantCoeff_eq_zero hF0]
end PI.AddIntG.Wk
