-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.neg_one_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:10.380304+00:00
-- url     : https://prove2.me/submissions/cd6af283-97e9-4605-b7a3-da3caeb3a161

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit

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
theorem _root_.solution (m j : ℕ) (hj : j ≤ m) :
    ((-1 : ℤ) ^ (m - j) : ℤ) = (-1) ^ m * (-1) ^ j := by
  rw [← pow_add]
  rw [show m + j = (m - j) + 2 * j by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
end PI.UnitaryGroupMassFormula.QmMove
