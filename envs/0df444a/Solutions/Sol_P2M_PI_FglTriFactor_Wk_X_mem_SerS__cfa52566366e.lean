-- Prove2me | solution 1 for P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:51.344676+00:00
-- url     : https://prove2.me/submissions/b8352be4-e4bf-408e-b65c-abcc97df1976

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]
namespace PI.FglTriFactor.Wk
theorem _root_.solution (S : Subring K) (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ∈ SerS S σ := by
  rw [PI.AddIntG.Wk.mem_SerS]
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem
end PI.FglTriFactor.Wk
