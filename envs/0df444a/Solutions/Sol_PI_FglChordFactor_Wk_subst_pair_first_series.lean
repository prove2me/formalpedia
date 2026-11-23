-- Prove2me | solution 1 for PI.FglChordFactor.Wk.subst_pair_first_series
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:57.292848+00:00
-- url     : https://prove2.me/submissions/aeec9537-1a35-4292-bc37-e25203b53347

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Theorems.Thm_PI_FglChordFactor_Wk_subst_pair_first_variable
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_psubst


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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS subst_mem_SerS subst_psubst)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f) =
      PowerSeries.subst u f := by
  rw [subst_psubst (PowerSeries.HasSubst.X 0) hs, subst_pair_first_variable hs]
end PI.FglChordFactor.Wk
