-- Prove2me | solution 1 for PI.HookSteps.Pn_last_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:37.073041+00:00
-- url     : https://prove2.me/submissions/aa2fe1e7-80ce-45c3-ad31-4a50505cfcd3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookNorm
import Theorems.Thm_PI_HookSteps_prod_Ioi_castSucc
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
theorem _root_.solution (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Pn ν = Pn (fun i : Fin n => ν (Fin.castSucc i)) * ∏ i : Fin n, (ν (Fin.castSucc i) + (n - i)) := by
  unfold Pn
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ j ∈ Finset.Ioi (Fin.last n), (ν (Fin.last n) - ν j + ((j : ℕ) - ((Fin.last n : Fin (n + 1)) : ℕ))) = 1 := by
    rw [Finset.eq_empty_of_forall_notMem fun j hj => absurd (Finset.mem_Ioi.mp hj) (not_lt.mpr (Fin.le_last j)), Finset.prod_empty]
  rw [hlast, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [prod_Ioi_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, h]
  congr 1 <;> omega
end PI.HookSteps
