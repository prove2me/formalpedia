-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.midC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:53.473914+00:00
-- url     : https://prove2.me/submissions/587c35d1-2ebe-4c12-acd2-9e1cac5b8dd8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance

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
variable {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (η : Fin n → A)
  (a : Fin (m + 1) → Fin n) (b : Fin m → Fin n) (w : ℂ)
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution (hη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0)
    (v v' : ℂ) (hv : v = v' + 1) (x d c : Fin n) :
    η c * Tm E v' x d - Tm E v x d * η c = -symC η d x c := by
  subst hv
  have h := hη x d c
  have hc : η c * algebraMap ℂ A v' = algebraMap ℂ A v' * η c := (Algebra.commutes _ _).symm
  have hk : η c * E x d = E x d * η c - (if c = d then η x else 0) := by
    have e : (if c = d then η x else 0) = (if d = c then η x else 0) := by
      by_cases hcd : c = d
      · rw [if_pos hcd, if_pos hcd.symm]
      · rw [if_neg hcd, if_neg (Ne.symm hcd)]
    rw [e, ← h]
    abel
  simp only [Tm, symC, mul_add, add_mul, hk]
  by_cases hxd : x = d
  · simp only [if_pos hxd]
    rw [hc, map_add, map_one, add_mul, one_mul]
    abel
  · simp only [if_neg hxd, mul_zero, zero_mul, zero_add]
    abel
end PI.UnitaryGroupMassFormula.QmMove
