-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.eL_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:18.149294+00:00
-- url     : https://prove2.me/submissions/4837572f-b128-4df8-a4c2-f0765cf04a1e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB

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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable (k j ρ : ℕ)
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (a : Fin j) : (eL k j ρ a).val = 2 * (j + ρ) + k - a.val := rfl
end PI.UnitaryCorollaryDerivatives.DjC
