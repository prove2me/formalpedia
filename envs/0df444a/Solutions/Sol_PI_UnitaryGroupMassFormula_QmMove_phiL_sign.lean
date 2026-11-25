-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.phiL_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:17.042963+00:00
-- url     : https://prove2.me/submissions/90e3a939-a119-45e7-8601-ae6f7fab61a9

import Definitions.Def_Formalism_PeriodIntegrals_QmDefs
import Definitions.Def_Formalism_PeriodIntegrals_QmMove
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermEqSumFirstColumnSplit
import Theorems.Thm_Formalism_REAL_sign_cycleToLast
import Theorems.Thm_Formalism_REAL_sign_extendLast


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
    Equiv.Perm.sign (lastColumnSplit m (j, ρ)) = (-1) ^ (m - (j : ℕ)) * Equiv.Perm.sign ρ := by
  simp [lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast]
end PI.UnitaryGroupMassFormula.QmMove
