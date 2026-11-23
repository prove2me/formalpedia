-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.firstColumnSplit_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:25.800901+00:00
-- url     : https://prove2.me/submissions/b01e2f6a-c5e7-4831-8df8-31bd61b4b006

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
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) (k : Fin m) :
    phi0 m (j, ρ) k.succ = j.succAbove (ρ k) := by
  simp [phi0, Equiv.Perm.mul_apply]
end PI.UnitaryGroupMassFormula.QmMove
