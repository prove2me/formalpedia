-- Prove2me | solution 1 for PI.UMultOne.UnitaryGroupMassFormula.tr_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:34.254729+00:00
-- url     : https://prove2.me/submissions/32680980-c300-4b18-96cb-4d3b0b2f8a83

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
theorem _root_.solution (m : ℕ) (x : Matrix.unitaryGroup (Fin m) ℂ) : tr m (tr m x) = x := by
  apply Subtype.ext
  simp only [tr_val, Matrix.transpose_transpose]
end PI.UMultOne.UnitaryGroupMassFormula
