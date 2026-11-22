-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.extN_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:49.839888+00:00
-- url     : https://prove2.me/submissions/99c94b2f-7b9e-4f6b-80c6-5db2dc70b205

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
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution {n m : ℕ} (b : Fin m → Fin n) (d : Fin n) (k : Fin m) : extN b d k = b k := by
  simp [extN, k.isLt]
end PI.UnitaryGroupMassFormula.QmMove
