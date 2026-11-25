-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.hJL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:28.50163+00:00
-- url     : https://prove2.me/submissions/6f7f31e6-9b95-49a9-90b6-25ed917e88d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (u x : Fin n → ℂ) : hJL ε u x = hJ ε u x := rfl
end PI.ScMuExists.UnitaryGroupMassFormula
