-- Prove2me | solution 1 for PI.AddIntG.Wk.G_wv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:07.175926+00:00
-- url     : https://prove2.me/submissions/f6034479-faa0-4d19-8ac3-d24d8d10d691

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) (i : Fin 2) :
    G W (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) (wv wq i) = 0 := by
  have hs : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.X i
  set φ := PowerSeries.substAlgHom (R := ℂ_[p]) hs with hφ
  have hX : (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = φ PowerSeries.X := by
    rw [hφ, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
  have hw : wv wq i = φ (wser wq) := by
    rw [hφ, PowerSeries.coe_substAlgHom]; rfl
  rw [hX, hw]
  have : G W (φ PowerSeries.X) (φ (wser wq)) = φ (G W PowerSeries.X (wser wq)) := by
    simp only [G, map_add, map_sub, map_mul, map_pow, AlgHom.commutes]
  rw [this, G_wser h, map_zero]
end PI.AddIntG.Wk
