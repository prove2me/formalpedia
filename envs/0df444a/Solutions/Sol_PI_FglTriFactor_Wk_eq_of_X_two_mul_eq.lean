-- Prove2me | solution 1 for PI.FglTriFactor.Wk.eq_of_X_two_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:06:35.075315+00:00
-- url     : https://prove2.me/submissions/a73757aa-0d37-4c0c-b439-d623e85aab3c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
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
theorem _root_.solution {f g : MvPowerSeries (Fin 3) ℂ_[p]} (h : MvPowerSeries.X 2 * f = MvPowerSeries.X 2 * g) :
    f = g := by
  refine mul_left_cancel₀ ?_ h
  intro h0
  have e := congrArg (MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) 1)) h0
  simp at e
end PI.FglTriFactor.Wk
