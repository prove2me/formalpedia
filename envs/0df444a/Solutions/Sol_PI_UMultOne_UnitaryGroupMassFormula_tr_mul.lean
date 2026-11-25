-- Prove2me | solution 1 for PI.UMultOne.UnitaryGroupMassFormula.tr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:25.636423+00:00
-- url     : https://prove2.me/submissions/6b89cd30-fa08-4bd4-a46b-fe3eab1b59d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
import Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_tr_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set
namespace PI.UMultOne.UnitaryGroupMassFormula
theorem _root_.solution (m : ℕ) (x y : Matrix.unitaryGroup (Fin m) ℂ) : tr m (x * y) = tr m y * tr m x := by
  apply Subtype.ext
  simp only [tr_val, Matrix.UnitaryGroup.mul_val, Matrix.transpose_mul]
end PI.UMultOne.UnitaryGroupMassFormula
