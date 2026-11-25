-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.Pv_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:25.789391+00:00
-- url     : https://prove2.me/submissions/fd493d97-3239-496f-a9ae-0e3a685364ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_extN_lt


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
    Pv E y a b w m τ = qminor E a (fun k => b (τ k.castSucc)) (w - 1) * y (b (τ (Fin.last m))) := by
  unfold Pv qminor
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
  have hf : Fv E y a b w m τ σ (Fin.last m) = y (b (τ (Fin.last m))) := by simp [Fv]
  have hg : (fun i : Fin m => Fv E y a b w m τ σ i.castSucc) =
      fun k : Fin m => Tm E (w - 1 - (k : ℂ)) (a (σ k)) (b (τ k.castSucc)) := by
    funext k
    simp only [Fv, Fin.val_castSucc]
    rw [if_neg (by have := k.isLt; omega), if_pos k.isLt, extN_lt] <;> rfl
  rw [hf, hg]
  exact (mul_assoc _ _ _).symm
end PI.UnitaryGroupMassFormula.QmMove
