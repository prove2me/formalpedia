-- Prove2me | solution 1 for PI.FglChordFactor.Wk.subst_bivariateSeries_difference_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:31.280414+00:00
-- url     : https://prove2.me/submissions/147a000c-11c0-46cc-8fde-72701455ac07

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
    MvPowerSeries.subst ![u, v] (sub l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = sub l ex u v := by
  have hA : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) l -
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [map_sub, cc_psubst (MvPowerSeries.constantCoeff_X 0), cc_psubst (MvPowerSeries.constantCoeff_X 1),
        hl0, sub_zero])
  unfold PI.FglChordFactor.sub PI.FglChordFactor.pt PI.FglChordFactor.lg
  rw [subst_psubst hA hs, ← MvPowerSeries.coe_substAlgHom hs, map_sub, MvPowerSeries.coe_substAlgHom,
    subst_pair_first_series hs, subst_pair_second_series hs]
end PI.FglChordFactor.Wk
