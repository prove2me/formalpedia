-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.phiL_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:12.188562+00:00
-- url     : https://prove2.me/submissions/6f23069e-ae9b-4950-91a0-89f42d0d6785

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Theorems.Thm_Formalism_REAL_cycleToLast_castSucc
import Theorems.Thm_Formalism_REAL_extendLast_castSucc


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
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) (k : Fin m) :
    lastColumnSplit m (j, ρ) k.castSucc = j.succAbove (ρ k) := by
  simp [lastColumnSplit, Equiv.Perm.mul_apply, extendLast_castSucc, cycleToLast_castSucc]
end PI.UnitaryGroupMassFormula.QmMove
