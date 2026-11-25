-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.move_operator_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:10:52.506888+00:00
-- url     : https://prove2.me/submissions/b5d155f8-a0e4-43d9-abde-6e001f9e42ff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_stepV
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_Mv_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_Mv_last
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_chain
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_fact_cancel
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_icomm
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_neg_one_pow_sub


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
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution : PI.MoveVec := by
  intro A _ _ n t E y hE hy _ a b w
  have hc := chain (Mv E y a b w) t (fun p hp => stepV E y a b w hy p hp)
  rw [Mv_last E y a b w hE, Mv_zero E y a b w hE] at hc
  have hs : ∀ X : Fin (t + 1) → A, ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (t - (j : ℕ)) : ℤ) : A) * X j =
      (((-1 : ℤ) ^ t : ℤ) : A) * ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * X j := by
    intro X
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [neg_one_pow_sub t j (Nat.lt_succ_iff.mp j.isLt), Int.cast_mul, mul_assoc]
  rw [hs, ← mul_assoc (((-1 : ℤ) ^ t : ℤ) : A), icomm ((-1 : ℤ) ^ t) (t.factorial : A), mul_assoc] at hc
  have h2 := fact_cancel t _ _ hc
  have hsq : (((-1 : ℤ) ^ t : ℤ) : A) * (((-1 : ℤ) ^ t : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, Int.cast_one]
  calc _ = ((((-1 : ℤ) ^ t : ℤ) : A) * (((-1 : ℤ) ^ t : ℤ) : A)) * ∑ j : Fin (t + 1),
        (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) := by
        rw [hsq, one_mul]
    _ = _ := by rw [mul_assoc, ← h2, ← mul_assoc, hsq, one_mul]
end PI.UnitaryGroupMassFormula.QmMove
