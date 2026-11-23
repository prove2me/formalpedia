-- Prove2me | solution 1 for PI.FglChordFactor.Wk.X_mem_SerS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:24.096937+00:00
-- url     : https://prove2.me/submissions/3c57385c-de71-4097-9874-30def0a006aa

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
theorem _root_.solution (S : Subring ℂ_[p]) (i : Fin 2) :
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
  rw [mem_SerS]; intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem
end PI.FglChordFactor.Wk
