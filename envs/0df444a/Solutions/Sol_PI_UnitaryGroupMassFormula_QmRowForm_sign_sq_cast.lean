-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.sign_sq_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:28.59619+00:00
-- url     : https://prove2.me/submissions/baf42cf3-f3ae-4441-be40-8a59bd39bfa0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_DoubleRowDecreasing

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
theorem _root_.solution {A : Type*} [Ring A] {t : ℕ} (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
end PI.UnitaryGroupMassFormula.QmRowForm
