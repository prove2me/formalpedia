-- Prove2me | solution 1 for PI.FglTriFactor.Wk.hasSubst_upd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:57.196432+00:00
-- url     : https://prove2.me/submissions/b93b6f55-4344-419c-a503-9df7d09aaa05

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Theorems.Thm_PI_FglTriFactor_Wk_upd_const
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
theorem _root_.solution (k : σ) {t : MvPowerSeries σ K} (ht : MvPowerSeries.constantCoeff t = 0) :
    MvPowerSeries.HasSubst (upd k t) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (upd_const ht)
end PI.FglTriFactor.Wk
