-- Prove2me | solution 1 for PI.AddIntG.Wk.flog_Fch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:43.170142+00:00
-- url     : https://prove2.me/submissions/072198d4-2dfb-40f3-8fbe-0f8f5818dea2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Theorems.Thm_PI_AddIntG_Wk_hasSubst_bZ
import Theorems.Thm_PI_AddIntG_Wk_Fch_eq
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst
import Theorems.Thm_P2M_PI_AddIntG_Wk_constantCoeff_flog__b4b5d000a5ef
import Theorems.Thm_PI_AddIntG_Wk_abel
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_thirdRoot


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
    PowerSeries.subst (Fch W wq) (flog W wq) =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) := by
  have hA := abel h
  have hb := hasSubst_bZ W wq
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hZ : PowerSeries.HasSubst (Z3 W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_thirdRoot W wq)
  have hB := congrArg (MvPowerSeries.substAlgHom (R := ℂ_[p]) hb) hA
  rw [map_add, map_add, map_zero, MvPowerSeries.coe_substAlgHom, subst_psubst (hX 0) hb,
    subst_psubst (hX 1) hb, subst_psubst hZ hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    ← Fch_eq] at hB
  have h0 : bZ W wq 0 = 0 := by simp [bZ]
  have h1' : bZ W wq 1 = Z3 W wq := by simp [bZ]
  rw [h0, h1', PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_flog' W wq)] at hB
  linear_combination hB - hA
end PI.AddIntG.Wk
