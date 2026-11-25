-- Prove2me | solution 1 for PI.HookSteps.prod_Ioi_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:08.744585+00:00
-- url     : https://prove2.me/submissions/e9d6ab61-ed8a-4a92-8a58-56b999fd158f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookNorm
import Theorems.Thm_PI_HookSteps_Ioi_eq_filter
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution {M : Type*} [CommMonoid M] (n : ℕ) (i : Fin n) (g : Fin (n + 1) → M) :
    ∏ j ∈ Finset.Ioi (Fin.castSucc i), g j = (∏ j ∈ Finset.Ioi i, g (Fin.castSucc j)) * g (Fin.last n) := by
  rw [Ioi_eq_filter, Ioi_eq_filter, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, if_true]
end PI.HookSteps
