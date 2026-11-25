-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.isClosed_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:12:18.600146+00:00
-- url     : https://prove2.me/submissions/0ff01a06-1cfc-4599-9898-49250cec4bad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution : IsClosed (UH (Hpk k r)) := by
  have hc : Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => gᴴ * Hpk k r * g :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq hc continuous_const
end PI.QuotSetU.UnitaryGroupMassFormula.SW
