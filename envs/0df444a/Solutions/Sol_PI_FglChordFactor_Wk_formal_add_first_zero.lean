-- Prove2me | solution 1 for PI.FglChordFactor.Wk.formal_add_first_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:39.266827+00:00
-- url     : https://prove2.me/submissions/4706a8e4-6567-434f-b5c2-05dd02d3b517

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_formal_add
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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]}
    (hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X) :
    MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = MvPowerSeries.X 1 := by
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hl : PowerSeries.HasSubst (flog W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (flog_const W wq)
  rw [subst_pair_formal_add (flog_const W wq) (hasSubst2 (map_zero _) (MvPowerSeries.constantCoeff_X 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [subst_zero_eq_zero_of_constantCoeff_zero (flog_const W wq), zero_add, ← PowerSeries.subst_comp_subst_apply hl hX1, hexl,
    PowerSeries.subst_X hX1]
end PI.FglChordFactor.Wk
