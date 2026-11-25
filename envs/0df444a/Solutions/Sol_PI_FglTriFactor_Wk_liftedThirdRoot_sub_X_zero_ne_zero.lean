-- Prove2me | solution 1 for PI.FglTriFactor.Wk.liftedThirdRoot_sub_X_zero_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:24.782139+00:00
-- url     : https://prove2.me/submissions/f87122e5-8976-456a-b388-e7fb2aa2ef38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Theorems.Thm_PI_FglTriFactor_Wk_pairSubst_zero_one_ne_zero
import Theorems.Thm_PI_FglTriFactor_Wk_liftedThirdRoot_sub_X
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_thirdRoot_sub_var_zero_ne_zero


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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    s3 W wq - MvPowerSeries.X 0 ≠ 0 := by
  intro h
  apply pairSubst_zero_one_ne_zero (PI.AddIntG.Wk.thirdRoot_sub_var_zero_ne_zero W wq)
  rw [← liftedThirdRoot_sub_X W wq 0]
  exact h
end PI.FglTriFactor.Wk
