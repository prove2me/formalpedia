-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.sgnlem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:16.557501+00:00
-- url     : https://prove2.me/submissions/3a985003-c342-4a7e-a5a6-c5af8fcbc43d

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
theorem _root_.solution {A : Type*} [Ring A] (z z' : ℤ) (x y : A) :
    ((z * z' : ℤ) : A) * (x * y) = (z : A) * (x * ((z' : A) * y)) := by
  rw [Int.cast_mul, mul_assoc, ← mul_assoc (z' : A) x y, (Int.cast_commute z' x).eq, mul_assoc]
end PI.UnitaryGroupMassFormula.QmMove
