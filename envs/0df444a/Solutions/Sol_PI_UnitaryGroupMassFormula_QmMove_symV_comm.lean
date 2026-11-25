-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.symV_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:50.395162+00:00
-- url     : https://prove2.me/submissions/d0b2f32b-55a3-49ab-ac9b-350a7168fe16

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
omit [Algebra ℂ A]
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution (x c d : Fin n) : symV y x c d = symV y x d c := by
  simp only [symV]; abel
end PI.UnitaryGroupMassFormula.QmMove
