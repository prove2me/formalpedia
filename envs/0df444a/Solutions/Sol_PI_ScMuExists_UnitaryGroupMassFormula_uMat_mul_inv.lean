-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.uMat_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:22.036804+00:00
-- url     : https://prove2.me/submissions/12a1d5e5-24a8-4680-88c6-4a5abce24e9e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply

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
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]
end PI.ScMuExists.UnitaryGroupMassFormula
