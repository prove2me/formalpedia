-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.sign_revConj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:16.981129+00:00
-- url     : https://prove2.me/submissions/747547d4-212a-4dba-8b79-89052f3fdde3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_DoubleRowIncreasing

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution {t : ℕ} (τ : Equiv.Perm (Fin t)) :
    Equiv.Perm.sign (revConj t τ) = Equiv.Perm.sign τ := by
  show Equiv.Perm.sign (Fin.revPerm * τ * Fin.revPerm) = _
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, mul_right_comm, Int.units_mul_self, one_mul]
end PI.UnitaryGroupMassFormula.QmRowForm
