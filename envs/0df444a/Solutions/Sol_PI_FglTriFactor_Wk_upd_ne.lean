-- Prove2me | solution 1 for PI.FglTriFactor.Wk.upd_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:44.796287+00:00
-- url     : https://prove2.me/submissions/7d139cf8-93cb-4a70-b9e0-42f70dcea8d8

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
theorem _root_.solution {k i : σ} (t : MvPowerSeries σ K) (h : i ≠ k) : upd k t i = MvPowerSeries.X i :=
  Function.update_of_ne h _ _
end PI.FglTriFactor.Wk
