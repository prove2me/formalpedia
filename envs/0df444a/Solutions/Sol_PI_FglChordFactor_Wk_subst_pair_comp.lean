-- Prove2me | solution 1 for PI.FglChordFactor.Wk.subst_pair_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:08.662206+00:00
-- url     : https://prove2.me/submissions/99e9e422-635b-4ed8-9e99-06f5d466f43b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
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
theorem _root_.solution {u v u' v' : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v])
    (hs' : MvPowerSeries.HasSubst ![u', v']) (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.subst ![u', v'] H) =
      MvPowerSeries.subst ![MvPowerSeries.subst ![u, v] u', MvPowerSeries.subst ![u, v] v'] H := by
  rw [MvPowerSeries.subst_comp_subst_apply hs' hs]
  congr 1
  funext i
  fin_cases i <;> simp
end PI.FglChordFactor.Wk
