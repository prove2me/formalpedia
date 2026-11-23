-- Prove2me | solution 1 for PI.FglTriFactor.Wk.pt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:26.189615+00:00
-- url     : https://prove2.me/submissions/45840d36-2313-46f7-9ca4-cbb8401a55a2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
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
variable {p : ℕ} [Fact p.Prime]
variable {l ex : PowerSeries ℂ_[p]} {σ τ : Type*}
namespace PI.FglTriFactor.Wk
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0) : pt ex (0 : MvPowerSeries σ ℂ_[p]) = 0 :=
  PowerSeries.subst_zero_of_constantCoeff_zero hex0
end PI.FglTriFactor.Wk
