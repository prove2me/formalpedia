-- Prove2me | solution 1 for PI.FglTriFactor.Wk.upd_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:45.165049+00:00
-- url     : https://prove2.me/submissions/e0fd94fa-8b7d-49ea-b8c7-d1977ef49b48

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
theorem _root_.solution (k : σ) (t : MvPowerSeries σ K) : upd k t k = t :=
  Function.update_self _ _ _
end PI.FglTriFactor.Wk
