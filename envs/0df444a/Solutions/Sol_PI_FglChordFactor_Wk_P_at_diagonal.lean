-- Prove2me | solution 1 for PI.FglChordFactor.Wk.P_at_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:04.375131+00:00
-- url     : https://prove2.me/submissions/18775cb9-6783-43d2-af87-708b0bf4fd39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstBivariateSeriesDifferencePair
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst2
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_first_series
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_first_variable
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_second_series
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_second_variable


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
theorem _root_.solution (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 0] (Pser wq) = 0 := by
  have hs := hasSubst2 (MvPowerSeries.constantCoeff_X 0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0) (MvPowerSeries.constantCoeff_X 0)
  unfold Pser
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sub, map_mul, map_mul, map_pow, map_pow,
    MvPowerSeries.coe_substAlgHom, subst_pair_first_variable hs, subst_pair_second_variable hs, subst_pair_first_series hs, subst_pair_second_series hs, sub_self]
end PI.FglChordFactor.Wk
