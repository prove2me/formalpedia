-- Prove2me | solution 1 for PI.FglTriFactor.Wk.pt_lg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:25.811382+00:00
-- url     : https://prove2.me/submissions/134d161e-99f8-4d8c-b894-82d55797823f

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
theorem _root_.solution (hl0 : PowerSeries.constantCoeff l = 0) (hinv : PowerSeries.subst l ex = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) : pt ex (lg l x) = x := by
  have hx' : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  unfold PI.FglTriFactor.lg PI.FglTriFactor.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0) hx', hinv,
    PowerSeries.subst_X hx']
end PI.FglTriFactor.Wk
