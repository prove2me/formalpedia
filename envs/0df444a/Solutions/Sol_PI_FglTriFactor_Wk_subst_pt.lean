-- Prove2me | solution 1 for PI.FglTriFactor.Wk.subst_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:40.534352+00:00
-- url     : https://prove2.me/submissions/e0be7b22-96bc-41b4-9fd4-b9a44052fcbb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Theorems.Thm_PI_FglTriFactor_Wk_psubst_comm
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
theorem _root_.solution {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst b (pt ex a) = pt ex (MvPowerSeries.subst b a) :=
  psubst_comm ha hb ex
end PI.FglTriFactor.Wk
