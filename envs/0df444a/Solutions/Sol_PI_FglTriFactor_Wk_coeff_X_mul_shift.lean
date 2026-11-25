-- Prove2me | solution 1 for PI.FglTriFactor.Wk.coeff_X_mul_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:43.711645+00:00
-- url     : https://prove2.me/submissions/14d7bf0b-d102-42e9-b3a6-fc2e7100c4f9

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
theorem _root_.solution (k : σ) (H : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e + Finsupp.single k 1) (MvPowerSeries.X k * H) = MvPowerSeries.coeff e H := by
  rw [add_comm, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul]
end PI.FglTriFactor.Wk
