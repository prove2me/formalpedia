-- Prove2me | solution 1 for PI.FglTriFactor.Wk.upd_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:09.083444+00:00
-- url     : https://prove2.me/submissions/22eccff7-593a-41d1-9925-8054cb0de109

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
theorem _root_.solution {k : σ} {t : MvPowerSeries σ K} (ht : MvPowerSeries.constantCoeff t = 0) (i : σ) :
    MvPowerSeries.constantCoeff (upd k t i) = 0 := by
  unfold upd
  rcases eq_or_ne i k with rfl | h
  · rw [Function.update_self]; exact ht
  · rw [Function.update_of_ne h]; exact MvPowerSeries.constantCoeff_X i
end PI.FglTriFactor.Wk
