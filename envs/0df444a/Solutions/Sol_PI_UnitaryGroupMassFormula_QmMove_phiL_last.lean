-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.phiL_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:13.89883+00:00
-- url     : https://prove2.me/submissions/792c4606-f14a-4ae4-a16e-d6d97fefbe27

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Theorems.Thm_Formalism_REAL_cycleToLast_last
import Theorems.Thm_Formalism_REAL_extendLast_last


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
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    lastColumnSplit m (j, ρ) (Fin.last m) = j := by
  simp [lastColumnSplit, Equiv.Perm.mul_apply, extendLast_last, cycleToLast_last]
end PI.UnitaryGroupMassFormula.QmMove
