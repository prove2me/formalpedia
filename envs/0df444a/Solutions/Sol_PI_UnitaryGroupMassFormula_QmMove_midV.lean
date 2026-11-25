-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.midV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:41:55.980431+00:00
-- url     : https://prove2.me/submissions/d7e38019-012d-4238-88b1-c474856fa1d0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared

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
theorem _root_.solution (hy : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (v v' : ℂ) (hv : v = v' + 1) (x d c : Fin n) :
    y c * Tm E v x d - Tm E v' x d * y c = symV y x c d := by
  have h := hy x d c
  rw [sub_eq_iff_eq_add] at h
  have c2 : ∀ z, algebraMap ℂ A v' * y z = y z * algebraMap ℂ A v' := fun z => Algebra.commutes _ _
  subst hv
  simp only [Tm, symV]
  split_ifs at h ⊢
  all_goals
    simp only [map_add, map_one, mul_add, add_mul, mul_one, zero_add, add_zero, h, c2]
    try noncomm_ring
end PI.UnitaryGroupMassFormula.QmMove
