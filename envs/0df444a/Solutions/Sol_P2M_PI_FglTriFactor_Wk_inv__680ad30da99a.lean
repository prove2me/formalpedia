-- Prove2me | solution 1 for P2M_PI_FglTriFactor_Wk_inv__680ad30da99a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:20.120219+00:00
-- url     : https://prove2.me/submissions/6010251c-98ca-4e3f-9c68-7db31766ee29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LogThirdPointSum
import Theorems.Thm_PI_FglTriFactor_Wk_cc_flog
import Theorems.Thm_PI_AddIntG_Wk_coeff_one_flog
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_left_inv


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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X) :
    PowerSeries.subst (flog W wq) ex = PowerSeries.X :=
  PI.AddIntG.Wk.subst_left_inv (cc_flog W wq) (PI.AddIntG.Wk.coeff_one_flog h) hex0 hex
end PI.FglTriFactor.Wk
