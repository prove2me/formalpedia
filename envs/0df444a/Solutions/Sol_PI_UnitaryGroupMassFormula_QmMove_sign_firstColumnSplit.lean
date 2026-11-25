-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.sign_firstColumnSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:25.758613+00:00
-- url     : https://prove2.me/submissions/59e7cd5c-51f7-4573-9034-5d720237579d

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
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) (ρ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (phi0 m (j, ρ)) = (-1) ^ (j : ℕ) * Equiv.Perm.sign ρ := by
  simp [phi0, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign]
end PI.UnitaryGroupMassFormula.QmMove
