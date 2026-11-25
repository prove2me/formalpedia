-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.move_operator_covariance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:35.373303+00:00
-- url     : https://prove2.me/submissions/16b71e74-4976-46f8-b6fb-17c803b7ca9f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_stepC
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_Nc_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_Nc_last

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
theorem _root_.solution : PI.MoveCov := by
  unfold PI.MoveCov
  intro A _ _ n t E η _ hη _ a b w
  have hit : ∀ p, p ≤ t → Nc E η a b w p = (-1 : A) ^ p * Nc E η a b w 0 := by
    intro p
    induction p with
    | zero => intro _; rw [pow_zero, one_mul]
    | succ p ih =>
      intro hp
      rw [stepC E η a b w hη p (by omega), ih (by omega), pow_succ, mul_neg_one, neg_mul]
  have h := hit t le_rfl
  rw [Nc_last, Nc_zero] at h
  have h2 : ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (η (a i) * qminor E (a ∘ i.succAbove) b (w - 1)) =
      (-1 : A) ^ t * ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (t - (j : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ j.succAbove) b w * η (a j)) := by
    rw [h, ← mul_assoc ((-1 : A) ^ t), ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc ((-1 : A) ^ t)]
  congr 1
  have hj := j.isLt
  push_cast
  rw [← pow_add, show t + (t - (j : ℕ)) = (j : ℕ) + 2 * (t - (j : ℕ)) by omega, pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]
end PI.UnitaryGroupMassFormula.QmMove
