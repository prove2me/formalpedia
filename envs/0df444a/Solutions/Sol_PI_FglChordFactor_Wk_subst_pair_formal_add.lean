-- Prove2me | solution 1 for PI.FglChordFactor.Wk.subst_pair_formal_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:53:20.482147+00:00
-- url     : https://prove2.me/submissions/88003064-1c27-43e2-b52b-52b5badb4d4a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_FglChordFactor_Wk_cc_psubst
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_first_series
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_second_series


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
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {l ex : PowerSeries ℂ_[p]} (hl0 : PowerSeries.constantCoeff l = 0)
    {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = add l ex u v := by
  have hA : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) l +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [map_add, cc_psubst (MvPowerSeries.constantCoeff_X 0), cc_psubst (MvPowerSeries.constantCoeff_X 1),
        hl0, add_zero])
  unfold PI.FglChordFactor.add PI.FglChordFactor.pt PI.FglChordFactor.lg
  rw [subst_psubst hA hs, ← MvPowerSeries.coe_substAlgHom hs, map_add, MvPowerSeries.coe_substAlgHom,
    subst_pair_first_series hs, subst_pair_second_series hs]
end PI.FglChordFactor.Wk
