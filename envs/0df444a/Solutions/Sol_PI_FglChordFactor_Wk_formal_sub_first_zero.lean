-- Prove2me | solution 1 for PI.FglChordFactor.Wk.formal_sub_first_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:03.496392+00:00
-- url     : https://prove2.me/submissions/f69917b7-371b-4065-b8fa-eea9a7bf5b5d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_FglChordFactor_Wk_subst_bivariateSeries_difference_pair
import Theorems.Thm_PI_FglChordFactor_Wk_negsub
import Theorems.Thm_PI_FglChordFactor_Wk_constantCoeff_inverse_variable
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst
import Theorems.Thm_PI_FglChordFactor_Wk_flog_const
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst2

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
namespace PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]
private theorem subst_zero_eq_zero_of_constantCoeff_zero {g : PowerSeries ℂ_[p]} (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (0 : MvPowerSeries (Fin 2) ℂ_[p]) g = 0 := by
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries (Fin 2) ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [hq, ← PowerSeries.coe_substAlgHom h0, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X h0,
    zero_mul]
end PI.FglChordFactor.Wk
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq)
    (hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X) :
    MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) := by
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hl : PowerSeries.HasSubst (flog W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (flog_const W wq)
  have hi : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_inverse_variable W wq 1)
  rw [subst_bivariateSeries_difference_pair (flog_const W wq) (hasSubst2 (map_zero _) (MvPowerSeries.constantCoeff_X 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [subst_zero_eq_zero_of_constantCoeff_zero (flog_const W wq), zero_sub, ← negsub hW hX1, ← PowerSeries.subst_comp_subst_apply hl hi,
    hexl, PowerSeries.subst_X hi]
end PI.FglChordFactor.Wk
