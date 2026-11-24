-- Prove2me | solution 1 for PI.FglTriFactor.Wk.lg_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:53:36.548855+00:00
-- url     : https://prove2.me/submissions/a62a03f0-bf2c-42c4-a107-43e841d16e74

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
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0) (hinv : PowerSeries.subst ex l = PowerSeries.X)
    {Y : MvPowerSeries σ ℂ_[p]} (hY : MvPowerSeries.constantCoeff Y = 0) : lg l (pt ex Y) = Y := by
  have hY' : PowerSeries.HasSubst Y := PowerSeries.HasSubst.of_constantCoeff_zero hY
  unfold PI.FglTriFactor.lg PI.FglTriFactor.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex0) hY', hinv,
    PowerSeries.subst_X hY']
end PI.FglTriFactor.Wk
