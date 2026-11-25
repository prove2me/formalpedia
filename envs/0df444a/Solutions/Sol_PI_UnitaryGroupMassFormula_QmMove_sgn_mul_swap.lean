-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.sgn_mul_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:22.77781+00:00
-- url     : https://prove2.me/submissions/41cacf51-8652-4d2e-9c05-c6625bcac359

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
theorem _root_.solution {A : Type*} [Ring A] {t : ℕ} (s : Equiv.Perm (Fin t))
    (hs : Equiv.Perm.sign s = -1) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign (τ * s) : ℤ) : A) = -((Equiv.Perm.sign τ : ℤ) : A) := by
  rw [Equiv.Perm.sign_mul, hs]
  push_cast
  simp
end PI.UnitaryGroupMassFormula.QmMove
