-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.Pv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:17.306069+00:00
-- url     : https://prove2.me/submissions/52a2bc45-95d4-4758-a239-5ec4f612694b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_extN_lt
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_icomm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
  (a : Fin m → Fin n) (b : Fin (m + 1) → Fin n) (w : ℂ)
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution (τ : Equiv.Perm (Fin (m + 1))) :
    Pv E y a b w 0 τ = y (b (τ 0)) * qminor E a (fun k => b (τ k.succ)) w := by
  unfold Pv qminor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [List.ofFn_succ, List.prod_cons]
  have hf : Fv E y a b w 0 τ σ 0 = y (b (τ 0)) := by simp [Fv]
  have hg : (fun i : Fin m => Fv E y a b w 0 τ σ i.succ) =
      fun k : Fin m => Tm E (w - (k : ℂ)) (a (σ k)) (b (τ k.succ)) := by
    funext k
    simp only [Fv, Fin.val_succ]
    rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, extN_lt] <;> rfl
  rw [hf, hg, ← mul_assoc, ← mul_assoc, icomm]
end PI.UnitaryGroupMassFormula.QmMove
