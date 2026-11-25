-- Prove2me | solution 1 for P2M_PI_FglTriFactor_Wk_abel__b380fdd8500c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:39.594693+00:00
-- url     : https://prove2.me/submissions/997b4f4c-f801-4c10-9b94-ef0582e086e1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LogThirdPointSum
import Theorems.Thm_PI_AddIntG_Wk_abel
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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglTriFactor.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    lg (flog W wq) (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) + lg (flog W wq) (MvPowerSeries.X 1) +
      lg (flog W wq) (Z3 W wq) = 0 := PI.AddIntG.Wk.abel h
end PI.FglTriFactor.Wk
